















import ctypes
import gc
import importlib
import io
import json
import os
import resource
import signal
import sys
import types
import unittest
from pathlib import Path

APP = Path(__file__).resolve().parent
sys.path.insert(0, str(APP))
sys.path.append(str(APP / "vdeps"))
SRC = Path(os.environ.get("RWX_SRC", APP / "sqlglot"))
OV = Path(os.environ.get("RWX_VERIFY_DIR", "/tmp/rwxv"))
TREE_DIRS = ("sqlglot", "tests")
REIMPORT_MS = 150
HANG_S = 60


def _mirror(src, dst):
    dst.mkdir(parents=True, exist_ok=True)
    for e in os.scandir(src):
        p = dst / e.name
        if e.is_dir(follow_symlinks=False) and e.name != "__pycache__":
            _mirror(Path(e.path), p)
        elif not p.exists():
            os.symlink(e.path, p)


def _cpu_children():
    r = resource.getrusage(resource.RUSAGE_CHILDREN)
    return r.ru_utime + r.ru_stime


class Server:
    def __init__(self):
        for d in TREE_DIRS:
            _mirror(SRC / d, OV / d)
        for f in os.scandir(SRC):
            if f.is_file() and not (OV / f.name).exists():
                os.symlink(f.path, OV / f.name)
        try:
            ctypes.CDLL(None).prctl(36, 1, 0, 0, 0)
        except Exception:
            pass
        sys.path.insert(0, str(OV))
        os.chdir(OV)
        os.cpu_count = lambda: 2
        os.process_cpu_count = lambda: 2
        self.ov = OV
        self.import_ran, self.opened = set(), set()
        self.loaded = set()
        self.funcs, self.lru = {}, []
        self.dirty = True
        ovs = str(OV)

        def hook(ev, args):
            if self.recording and ev == "open" and args and isinstance(args[0], (str, bytes, os.PathLike)):
                f = os.path.abspath(os.fsdecode(args[0]))
                if f.startswith(ovs):
                    self.opened.add(os.path.relpath(f, ovs).replace("\\", "/"))
        self.recording = False
        sys.addaudithook(hook)
        self._import(["sqlglot"])

    def _import(self, mods):
        mon = sys.monitoring
        tool = 3
        mon.use_tool_id(tool, "vserve")

        def on_start(code, off):
            self.import_ran.add((code.co_filename, code.co_qualname, code.co_firstlineno))
            return mon.DISABLE
        mon.register_callback(tool, mon.events.PY_START, on_start)
        mon.set_events(tool, mon.events.PY_START)
        self.recording = True
        out, err = sys.stdout, sys.stderr
        sys.stdout = sys.stderr = io.StringIO()
        try:
            for m in mods:
                try:
                    importlib.import_module(m)
                except Exception:
                    pass
                self.loaded.add(m)
        finally:
            sys.stdout, sys.stderr = out, err
            self.recording = False
            mon.set_events(tool, 0)
            mon.free_tool_id(tool)
        self.dirty = True

    def _scan(self):
        ovs = str(OV)
        self.funcs, self.lru = {}, []
        for obj in gc.get_objects():
            if type(obj).__name__ == "_lru_cache_wrapper":
                self.lru.append(obj)
            elif type(obj) is types.FunctionType:
                c = obj.__code__
                if c.co_filename.startswith(ovs):
                    self.funcs.setdefault((c.co_filename, c.co_qualname, c.co_firstlineno), []).append(obj)
        self.dirty = False

    def handle(self, req):
        import selector as S
        import verify as V
        tests = req["tests"]
        mods = sorted({t.split("::")[0][:-3].replace("/", ".") for t in tests} - self.loaded)
        if mods:
            self._import(mods)
        if self.dirty:
            self._scan()
        fds = S.parse_patch(req["patch"])
        files = []
        for f in fds:
            if f["binary"] or not f["old"] or not f["new"] or f["old"] != f["new"]:
                return "unknown", "unsupported diff"
            rel = f["old"]
            if not rel.startswith(TREE_DIRS):
                return "unknown", f"{rel} outside the mirrored tree"
            old = (SRC / rel).read_text(encoding="utf-8")
            new, _, _ = S.apply_hunks(old, f["hunks"])
            files.append((rel, old, new))
        mode, detail = V.Verifier.plan(self, files)
        if mode != "swap" and REIMPORT_MS > req.get("max_start_ms", 0):
            return "unknown", f"re-import not worth it: {detail}"
        written = []
        try:
            for rel, old, new in files:
                p = OV / rel
                os.unlink(p)
                written.append(p)
                p.write_text(new, encoding="utf-8", newline="")
            return self._run(mode, detail, tests, int(req["cpu_s"]))
        finally:
            for p in written:
                try:
                    os.unlink(p)
                except FileNotFoundError:
                    pass
                os.symlink(SRC / p.relative_to(OV), p)

    def _run(self, mode, swaps, tests, cpu_s):
        rfd, wfd = os.pipe()
        pid = os.fork()
        if pid == 0:
            os.close(rfd)
            res = "unknown"
            try:
                os.setpgid(0, 0)
                nul = os.open(os.devnull, os.O_RDWR)
                for fd in (0, 1, 2):
                    os.dup2(nul, fd)
                resource.setrlimit(resource.RLIMIT_CPU, (cpu_s, cpu_s + 1))
                signal.alarm(HANG_S)
                sys.dont_write_bytecode = True


                import multiprocessing.context as mpc
                mpc._concrete_contexts["spawn"] = mpc._concrete_contexts["fork"]
                if mode == "swap":
                    import verify as V
                    V.Verifier._do_swaps(self, swaps)
                else:
                    for m in list(sys.modules):
                        if m == "sqlglot" or m.startswith(("sqlglot.", "tests")):
                            del sys.modules[m]
                    importlib.invalidate_caches()
                res = _run_failfast(tests)
            except BaseException as e:
                res = f"unknown {type(e).__name__}"
            os.write(wfd, res.encode()[:200])
            os._exit(0)
        os.close(wfd)
        data = b""
        while True:
            ch = os.read(rfd, 4096)
            if not ch:
                break
            data += ch
        os.close(rfd)
        os.waitpid(pid, 0)
        try:
            os.killpg(pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
        while True:
            try:
                if os.waitpid(-1, os.WNOHANG)[0] == 0:
                    break
            except ChildProcessError:
                break
        res = data.decode() or "unknown no result"
        return ("pass", mode) if res == "pass" else (res.split(" ", 1)[0], f"{mode}: {res}")


def _run_failfast(tests):


    groups = []
    for t in tests:
        f, cls, meth = t.split("::")
        key = (f[:-3].replace("/", "."), cls)
        if groups and groups[-1][0] == key:
            groups[-1][1].append(meth)
        else:
            groups.append((key, [meth]))
    for (mod, cls), meths in groups:
        try:
            C = getattr(importlib.import_module(mod), cls)
        except BaseException as e:
            return f"fail import {mod}: {type(e).__name__}"
        suite = unittest.TestSuite([C(m) for m in meths])
        r = unittest.TestResult()
        r.failfast = True
        out, err = sys.stdout, sys.stderr
        sys.stdout = sys.stderr = io.StringIO()
        try:
            suite.run(r)
        finally:
            sys.stdout, sys.stderr = out, err
        if r.failures or r.errors or r.unexpectedSuccesses or r.shouldStop or r.testsRun != len(meths):
            return f"fail {mod}.{cls} ran {r.testsRun}/{len(meths)}"
    return "pass"


def measure(tests_json, out_path, max_rec_s=1.0, par=4):


    tests = [t for t in json.loads(Path(tests_json).read_text(encoding="utf-8"))["tests"] if t["seconds"] <= max_rec_s]
    srv = Server()
    srv._import(sorted({t["file"][:-3].replace("/", ".") for t in tests}))
    import multiprocessing.context as mpc
    out, running, todo = {}, {}, list(tests)
    while todo or running:
        while todo and len(running) < par:
            t = todo.pop()
            pid = os.fork()
            if pid == 0:
                try:
                    os.setpgid(0, 0)
                    nul = os.open(os.devnull, os.O_RDWR)
                    for fd in (0, 1, 2):
                        os.dup2(nul, fd)
                    resource.setrlimit(resource.RLIMIT_CPU, (10, 11))
                    signal.alarm(HANG_S)
                    mpc._concrete_contexts["spawn"] = mpc._concrete_contexts["fork"]
                    _run_failfast([t["id"]])
                finally:
                    os._exit(0)
            running[pid] = t
        pid, _, ru = os.wait4(-1, 0)
        t = running.pop(pid, None)
        if t is not None:
            out[t["id"]] = round((ru.ru_utime + ru.ru_stime) * 1000)
    Path(out_path).write_text(json.dumps(out), encoding="utf-8")


def main():
    if sys.argv[1:2] == ["measure"]:
        measure(sys.argv[2], sys.argv[3])
        return
    gc.disable()
    srv = Server()
    boot = round(sum(os.times()[:2]) * 1000)
    sys.stdout.write(json.dumps({"ready": True, "cpu_ms": boot}) + "\n")
    sys.stdout.flush()
    for line in sys.stdin:
        c0 = _cpu_children() + sum(os.times()[:2])
        try:
            verdict, why = srv.handle(json.loads(line))
        except BaseException as e:
            verdict, why = "unknown", f"server error {type(e).__name__}: {e}"
        cpu_ms = round((_cpu_children() + sum(os.times()[:2]) - c0) * 1000)
        sys.stdout.write(json.dumps({"verdict": verdict, "why": why[:200], "cpu_ms": cpu_ms}) + "\n")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
