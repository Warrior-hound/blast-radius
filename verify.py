












import gc
import importlib
import io
import json
import os
import shutil
import signal
import sys
import time
import types
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import selector as S

COPY_DIRS = ("sqlglot", "tests")


def _key(co):
    return (co.co_qualname, co.co_firstlineno)


class Verifier:
    def __init__(self, src_root, overlay, test_ids):
        self.src = Path(src_root)
        self.ov = Path(overlay)
        if not (self.ov / "sqlglot").exists():
            self.ov.mkdir(parents=True, exist_ok=True)
            for d in COPY_DIRS:
                shutil.copytree(self.src / d, self.ov / d, symlinks=True,
                                ignore=shutil.ignore_patterns(".git"))
        sys.path.insert(0, str(self.ov))
        os.chdir(self.ov)

        self.import_ran = set()
        self.opened = set()
        mon = sys.monitoring
        tool = 3
        mon.use_tool_id(tool, "verify")

        def on_start(code, off):
            self.import_ran.add((code.co_filename, code.co_qualname, code.co_firstlineno))
            return mon.DISABLE

        mon.register_callback(tool, mon.events.PY_START, on_start)
        mon.set_events(tool, mon.events.PY_START)
        ovs = str(self.ov)

        self.recording = True

        def hook(ev, args):
            if self.recording and ev == "open" and args and isinstance(args[0], str) and args[0].startswith(ovs):
                self.opened.add(os.path.relpath(args[0], ovs).replace("\\", "/"))

        sys.addaudithook(hook)
        import sqlglot
        self.mods = sorted({t.split("::")[0][:-3].replace("/", ".") for t in test_ids})
        self.import_errors = {}
        for m in self.mods:
            try:
                importlib.import_module(m)
            except Exception as e:
                self.import_errors[m] = repr(e)
        mon.set_events(tool, 0)
        mon.free_tool_id(tool)
        self.recording = False
        gc.collect()
        ovs_ = str(self.ov)
        self.funcs = {}
        self.lru = []
        for obj in gc.get_objects():
            if type(obj).__name__ == "_lru_cache_wrapper":
                self.lru.append(obj)
            elif type(obj) is types.FunctionType:
                c = obj.__code__
                if c.co_filename.startswith(ovs_):
                    self.funcs.setdefault((c.co_filename, c.co_qualname, c.co_firstlineno), []).append(obj)
        gc.freeze()


    def plan(self, files):

        swaps = []
        why = None
        for rel, old, new in files:
            path = str(self.ov / rel)
            if not rel.endswith(".py"):
                if rel in self.opened:
                    why = f"{rel} read at import"
                continue
            modname = rel[:-3].replace("/", ".")
            if modname.endswith(".__init__"):
                modname = modname[:-9]
            if modname not in sys.modules:
                continue
            try:
                nco = compile(new, path, "exec", dont_inherit=True)
            except (SyntaxError, ValueError):
                return "reimport", f"{rel} syntax"
            oco = compile(old, path, "exec", dont_inherit=True)
            om, nm = S._walk(oco, "", {}), S._walk(nco, "", {})
            if set(om) != set(nm):
                return "reimport", f"{rel} code objects added/removed"
            changed = [k for k in om if S._own_signature(om[k]) != S._own_signature(nm[k])]
            for k in changed:

                parts = k.split("/")
                target = None
                for i in range(1, len(parts) + 1):
                    kk = "/".join(parts[:i])
                    co = om[kk]
                    if co.co_flags & 0x0002:
                        target = kk
                        break
                if target is None:
                    return "reimport", f"{rel} scope-level change ({om[k].co_qualname})"
                o = om[target]
                if (path, o.co_qualname, o.co_firstlineno) in self.import_ran:
                    return "reimport", f"{rel} {o.co_qualname} ran at import"
                if om[target].co_freevars != nm[target].co_freevars:
                    return "reimport", f"{rel} freevars changed"
                swaps.append((path, om[target], nm[target]))
        if why:
            return "reimport", why
        return "swap", swaps

    def _do_swaps(self, swaps):
        want = {}
        for path, o, n in swaps:
            want.setdefault((path, o.co_qualname, o.co_firstlineno), []).append((o, n))
        hits = {k: 0 for k in want}
        for k, cands in want.items():
            for obj in self.funcs.get(k, ()):
                c = obj.__code__
                sig = S._own_signature(c)
                m = [n for o, n in cands if S._own_signature(o) == sig]
                if len(m) != 1:
                    raise RuntimeError(f"ambiguous swap {k}")
                obj.__code__ = m[0]
                hits[k] += 1
        missing = [k for k, v in hits.items() if v == 0]
        if missing:
            raise RuntimeError(f"no live function for {missing}")
        for obj in self.lru:
            if True:
                try:
                    obj.cache_clear()
                except Exception:
                    pass


    def verify(self, patch_text, test_ids, timeout_s=60):

        info = {}
        try:
            fds = S.parse_patch(patch_text)
            files = []
            for f in fds:
                if f["binary"] or not f["old"] or not f["new"] or f["old"] != f["new"]:
                    return {t: "unknown" for t in test_ids}, {"why": "unsupported diff"}
                rel = f["old"]
                if not rel.startswith(COPY_DIRS):
                    continue
                old = (self.ov / rel).read_text(encoding="utf-8")
                new, _, _ = S.apply_hunks(old, f["hunks"])
                files.append((rel, old, new))
            mode, detail = self.plan(files)
        except Exception as e:
            return {t: "unknown" for t in test_ids}, {"why": f"plan error {e!r}"}
        info["mode"] = mode
        info["detail"] = detail if mode == "reimport" else len(detail)
        saved = []
        for rel, old, new in files:
            p = self.ov / rel
            st = p.stat()
            saved.append((p, old, st))
            p.write_text(new, encoding="utf-8", newline="")
            os.utime(p, ns=(st.st_atime_ns, st.st_mtime_ns + 7_777_000_000_000))
        resf = self.ov.parent / f"vres_{os.getpid()}.json"
        if resf.exists():
            resf.unlink()
        pid = os.fork()
        if pid == 0:
            code = 0
            try:
                os.setpgid(0, 0)
                signal.alarm(int(timeout_s))
                if os.environ.get("VERIFY_DEBUG"):
                    import faulthandler
                    faulthandler.dump_traceback_later(max(1, timeout_s - 5), file=sys.__stderr__)
                os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
                sys.dont_write_bytecode = True
                os.process_cpu_count = lambda: 2
                os.cpu_count = lambda: 2
                if os.environ.get("VERIFY_FORKPOOL") == "1":


                    import multiprocessing.context as mpc
                    mpc._concrete_contexts["spawn"] = mpc._concrete_contexts["fork"]
                if mode == "reimport":
                    for m in list(sys.modules):
                        if m == "sqlglot" or m.startswith(("sqlglot.", "tests")):
                            del sys.modules[m]
                    importlib.invalidate_caches()
                else:
                    self._do_swaps(detail)
                res = run_tests(test_ids)
            except BaseException as e:
                res = {"__error__": repr(e)}
            tmpf = str(resf) + ".part"
            with open(tmpf, "w") as fh:
                json.dump(res, fh)
            os.replace(tmpf, resf)
            os._exit(code)
        os.waitpid(pid, 0)
        try:
            os.killpg(pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
        for p, old, st in saved:
            p.write_text(old, encoding="utf-8", newline="")
            os.utime(p, ns=(st.st_atime_ns, st.st_mtime_ns))
        try:
            res = json.loads(resf.read_text())
            resf.unlink()
        except (OSError, ValueError):
            res = {}
        if "__error__" in res:
            info["error"] = res["__error__"]
        return {t: res.get(t, "unknown") for t in test_ids}, info


class _Result(unittest.TestResult):
    def __init__(self):
        super().__init__()
        self.bad = set()

    def _id(self, test):
        return getattr(test, "_vid", None)

    def addError(self, test, err):
        super().addError(test, err)
        self._mark(test)

    def addFailure(self, test, err):
        super().addFailure(test, err)
        self._mark(test)

    def addSubTest(self, test, subtest, err):
        super().addSubTest(test, subtest, err)
        if err is not None:
            self._mark(test)

    def addUnexpectedSuccess(self, test):
        super().addUnexpectedSuccess(test)
        self._mark(test)

    def _mark(self, test):
        vid = self._id(test)
        if vid is None:
            desc = str(test)
            self.bad.add(("class", desc))
        else:
            self.bad.add(("test", vid))


def run_tests(test_ids):

    verdict = {}
    by_class = {}
    order = []
    for t in test_ids:
        f, cls, meth = t.split("::")
        key = (f[:-3].replace("/", "."), cls)
        if key not in by_class:
            by_class[key] = []
            order.append(key)
        by_class[key].append((meth, t))
    for mod, cls in order:
        items = by_class[(mod, cls)]
        try:
            m = importlib.import_module(mod)
            C = getattr(m, cls)
        except Exception:
            for _, t in items:
                verdict[t] = "fail"
            continue
        suite = unittest.TestSuite()
        for meth, t in items:
            try:
                tc = C(meth)
            except Exception:
                verdict[t] = "unknown"
                continue
            tc._vid = t
            suite.addTest(tc)
        res = _Result()
        out, err = sys.stdout, sys.stderr
        sys.stdout = sys.stderr = io.StringIO()
        try:
            suite.run(res)
        finally:
            sys.stdout, sys.stderr = out, err
        class_fail = any(k == "class" for k, _ in res.bad)
        ran = {getattr(x, "_vid", None) for x in suite._tests if x is not None} if not suite._cleanup else None
        for meth, t in items:
            if t in verdict:
                continue
            if class_fail or ("test", t) in res.bad:
                verdict[t] = "fail"
            else:
                verdict[t] = "pass"

        _ = ran
    return verdict
