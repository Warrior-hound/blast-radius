













import gzip
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

CHILD_TIMEOUT_S = float(os.environ.get("RWX_E1_TIMEOUT_S", "60"))

_SCALARS = (type(None), bool, int, float, complex, str, bytes)


def _fields(o):


    t = type(o)
    out = []
    for c in t.__mro__:
        sl = c.__dict__.get("__slots__", ())
        if isinstance(sl, str):
            sl = (sl,)
        for n in sl:
            if n not in ("__dict__", "__weakref__", "_hash"):
                out.append((n, getattr(o, n, _UNSET)))
    d = getattr(o, "__dict__", None)
    if isinstance(d, dict):
        out += [(str(k), v) for k, v in d.items()]
    return out


class _Mark:
    __slots__ = ("s",)

    def __init__(self, s):
        self.s = s


_UNSET = _Mark("<unset>")


def _atom(o):

    import enum
    import types as T
    t = type(o)
    if t in _SCALARS:
        return t.__name__[0] + repr(o)
    if t is _Mark:
        return o.s
    if isinstance(o, type):
        return f"T{o.__module__}.{o.__qualname__}"
    if isinstance(o, enum.Enum):
        return f"N{t.__module__}.{t.__qualname__}.{o.name}"
    if isinstance(o, (T.FunctionType, T.BuiltinFunctionType, T.MethodType, T.ModuleType)):
        return f"F{getattr(o, '__module__', '')}.{getattr(o, '__qualname__', getattr(o, '__name__', ''))}"
    return None


def _children(o, t):

    if t in (list, tuple):
        return f"{t.__name__[0]}[{len(o)}", list(o)
    if isinstance(o, dict):
        items = []
        for k, v in o.items():
            items += (k, v)
        return f"d{t.__qualname__}[{len(o)}", items
    vals = []
    for n, v in _fields(o):
        vals += (_Mark("." + n), v)
    if not vals:
        vals.append(_Mark("r" + repr(o)))
    return f"O{t.__module__}.{t.__qualname__}[", vals


def _shallow(o):
    a = _atom(o)
    if a is not None:
        return a
    t = type(o)
    parts = [t.__qualname__]
    if not isinstance(o, (list, tuple, dict, set, frozenset)):
        for n, v in _fields(o):
            a = _atom(v)
            if a is not None:
                parts.append(n + "=" + a)
    return "|".join(parts)


def _order_key(o, cache, rounds=3):


    k = cache.get((id(o), rounds))
    if k is not None:
        return k
    k = _base_key(o, cache)
    if rounds > 0 and _atom(o) is None and not isinstance(o, (list, tuple, dict, set, frozenset)):
        for n, v in _fields(o):
            if isinstance(v, (set, frozenset)):
                k += "" + n + ":" + "".join(sorted(_order_key(m, cache, rounds - 1) for m in v))
    cache[(id(o), rounds)] = k
    return k


def _base_key(o, cache):


    i = id(o)
    k = cache.get(i)
    if k is not None:
        return k
    out, memo, stack = [], {}, [o]
    while stack:
        x = stack.pop()
        a = _atom(x)
        if a is not None:
            out.append(a)
            continue
        if id(x) in memo:
            out.append(f"@{memo[id(x)]}")
            continue
        memo[id(x)] = len(memo)
        t = type(x)
        if isinstance(x, (set, frozenset)):
            out.append("s[" + ",".join(sorted(_shallow(y) for y in x)) + "]")
            continue
        tok, kids = _children(x, t)
        if tok.startswith("O"):
            kids = [v for j, v in enumerate(kids)
                    if not (j % 2 == 0 and type(v) is _Mark and v.s == ".parent")
                    and not (j % 2 == 1 and type(kids[j - 1]) is _Mark and kids[j - 1].s == ".parent")]
        out.append(tok)
        stack.append(_Mark("]"))
        stack.extend(reversed(kids))
    k = cache[i] = "\x1f".join(out)
    return k


def _sorted_set(o, keys):

    groups = {}
    for y in o:
        groups.setdefault(_shallow(y), []).append(y)
    out = []
    for k in sorted(groups):
        g = groups[k]
        out += g if len(g) == 1 else sorted(g, key=lambda y: _order_key(y, keys))
    return out


_TYPE_INFO = {}


def _type_info(t):

    info = _TYPE_INFO.get(t)
    if info is None:
        import enum
        import types as T
        if t in _SCALARS or t is _Mark or issubclass(t, (type, enum.Enum, T.FunctionType,
                                                          T.BuiltinFunctionType, T.MethodType, T.ModuleType)):
            info = (0, "", ())
        elif issubclass(t, (list, tuple)):
            info = (1, t.__name__[0], ())
        elif issubclass(t, dict):
            info = (2, "d" + t.__qualname__, ())
        elif issubclass(t, (set, frozenset)):
            info = (3, "s" + t.__qualname__, ())
        else:
            names = []
            for c in t.__mro__:
                sl = c.__dict__.get("__slots__", ())
                if isinstance(sl, str):
                    sl = (sl,)
                names += [n for n in sl if n not in ("__dict__", "__weakref__", "_hash")]
            info = (4, f"O{t.__module__}.{t.__qualname__}:{','.join(names)}", tuple(names))
        _TYPE_INFO[t] = info
    return info


def canon(root):






    out, memo, keep, keys = [], {}, [], {}
    push_out = out.append
    stack = [root]
    pop, extend = stack.pop, stack.extend
    while stack:
        o = pop()
        t = type(o)
        if t is str:
            push_out("s" + repr(o))
            continue
        kind, head, names = _type_info(t)
        if kind == 0:
            push_out(_atom(o))
            continue
        i = id(o)
        r = memo.get(i)
        if r is not None:
            push_out(f"@{r}")
            continue
        memo[i] = len(memo)
        keep.append(o)
        if kind == 1:
            push_out(f"{head}{len(o)}")
            extend(reversed(o))
        elif kind == 2:
            push_out(f"{head}{len(o)}")
            items = []
            for k, v in o.items():
                items += (k, v)
            extend(reversed(items))
        elif kind == 3:
            push_out(f"{head}{len(o)}")
            extend(reversed(_sorted_set(o, keys)))
        else:
            vals = [getattr(o, n, _UNSET) for n in names]
            d = getattr(o, "__dict__", None)
            if isinstance(d, dict):
                push_out(head + "+" + ",".join(map(str, d)))
                vals += d.values()
            else:
                push_out(head)
            if not vals:
                push_out("r" + repr(o))
            extend(reversed(vals))
    return out


def digest(parts):
    h = hashlib.sha256()
    for p in parts:
        h.update(p.encode("utf-8", "surrogatepass"))
        h.update(b"\x1e")
    return h.hexdigest()[:32]




FIXTURE = {"tpcds": ("optimizer/tpc-ds/tpc-ds.sql", "TPCDS_SCHEMA"),
           "tpch": ("optimizer/tpc-h/tpc-h.sql", "TPCH_SCHEMA"),
           "opt_tpch": ("optimizer/tpc-h/tpc-h.sql", None)}


def boundary(kind, sql, meta, optimized, schema_dict):

    import pickle
    from sqlglot import find_tables, parse_one, transpile
    from sqlglot.optimizer import optimize
    from sqlglot.planner import Plan
    from sqlglot.schema import ensure_schema
    parts = []
    try:
        if kind == "opt_tpch":
            parts.append("D" + transpile(sql, write="duckdb")[0])
            parts.append("D" + transpile(optimized, write="duckdb")[0])
            return digest(parts)


        e = pickle.loads(pickle.dumps(parse_one(sql)))
        parts.append("parsed")
        if meta.get("execute"):
            parts.append("tables:" + json.dumps(sorted(t.name for t in find_tables(e))))
            schema = ensure_schema(schema_dict, dialect=None)
            plan = Plan(optimize(e, schema, leave_tables_isolated=True, dialect=None))
            parts += canon(plan)
            parts += canon(schema.supported_table_args)
            parts.append("D" + transpile(sql, write="duckdb")[0])
    except Exception as ex:
        parts.append(f"EXC {type(ex).__module__}.{type(ex).__qualname__}")
    return digest(parts)


def load_queries(kind):
    from tests import helpers
    fname, schema_name = FIXTURE[kind]
    qs = list(helpers.load_sql_fixture_pairs(fname))
    schema = getattr(helpers, schema_name) if schema_name else None
    return qs, schema




_E1_SETUP = r"""
import importlib, importlib.abc, importlib.util, json, sys
patched = {}
class Finder(importlib.abc.MetaPathFinder, importlib.abc.Loader):
    def find_spec(self, name, path, target=None):
        if name in patched:
            return importlib.util.spec_from_loader(name, self, origin=patched[name][2], is_package=patched[name][1])
        return None
    def create_module(self, spec):
        return None
    def exec_module(self, module):
        src, is_pkg, origin = patched[module.__name__]
        if is_pkg:
            module.__path__ = [origin.rsplit("/", 1)[0]]
        module.__file__ = origin
        exec(compile(src, origin, "exec"), module.__dict__)
root, app = sys.argv[2], sys.argv[3]
sys.setrecursionlimit(900)  # below the real tests' default 1000 (pytest adds frames): deeper recursion must differ -> keep
sys.path.insert(0, root)
sys.meta_path.insert(0, Finder())
sys.path.insert(0, app)
import e1_cutoff as E
"""

_E1_WORK = r"""
cfg = json.load(open(sys.argv[1], encoding="utf-8"))
patched.update(cfg["patched"])
fx = cfg.get("fixtures") or {}
out = {}
if fx:
    # patched fixture texts, served to tests.helpers' own loader (it opens them by path)
    import builtins, io, os.path
    from tests import helpers as _h
    _paths = {os.path.normpath(os.path.join(_h.FIXTURES_DIR, f)): t for f, t in fx.items()}
    def _open(file, *a, **k):
        t = _paths.get(os.path.normpath(str(file)))
        return io.StringIO(t) if t is not None else builtins.open(file, *a, **k)
    _h.open = _open
    def _pairs(f, patched_fx):
        saved = _h.open
        _h.open = _open if patched_fx else builtins.open
        try:
            return list(_h.load_sql_fixture_pairs(f))
        finally:
            _h.open = saved
    # the test class loads every fixture at class set-up: each patched one must still load, and the
    # SQL text it shares with the other fixtures (the class's result cache is keyed by it) must not change
    allf = sorted({v[0] for v in E.FIXTURE.values()})
    chk = {}
    for f in fx:
        try:
            new = {q[1] for q in _pairs(f, True)}
            old = {q[1] for q in _pairs(f, False)}
            others = set()
            for g in allf:
                if g != f:
                    others |= {q[1] for q in _pairs(g, True)}
            chk[f] = (new & others) == (old & others)
        except Exception:
            chk[f] = False
    out["_fixtures"] = chk
for kind, spec in cfg["work"].items():
    qs, schema = E.load_queries(kind)
    exp = cfg.get("expect", {}).get(kind)
    out[kind] = {"_n": len(qs)}
    idx = set(range(len(qs))) if spec["idx"] == "all" else set(spec["idx"])
    if spec.get("changed"):
        # queries whose fixture entry changed (same position, other text); a count change keeps the test
        old = _pairs(E.FIXTURE[kind][0], False)
        if len(old) != len(qs):
            idx = set(range(len(qs)))
        else:
            idx |= {i for i in range(len(qs)) if tuple(old[i]) != tuple(qs[i])}
    out[kind]["_idx"] = sorted(idx)
    for i in sorted(idx):
        if i >= len(qs):
            out[kind]["_n"] = -1
            break
        d = out[kind][str(i)] = E.boundary(kind, qs[i][1], qs[i][0], qs[i][2], schema)
        if exp is not None and (i >= len(exp) or d != exp[i]):
            break  # one difference settles it: keep the test
print(json.dumps(out))
"""

_CHILD = _E1_SETUP + _E1_WORK







_E1_SERVER = _E1_SETUP + r"""
import os
class _Asked(importlib.abc.MetaPathFinder):
    def find_spec(self, name, path, target=None):
        _asked.add(name)
        return None
_asked = set()
_rec = _Asked()
sys.meta_path.insert(0, _rec)
_ok = True
try:
    import sqlglot
except BaseException:
    _ok = False
sys.meta_path.remove(_rec)
_asked |= set(sys.modules)
sys.stdout.flush()
sys.stderr.flush()
os.write(1, (json.dumps({"ok": _ok, "asked": sorted(_asked)}) + "\n").encode())
_inp = sys.stdin.buffer
while _ok:
    _line = _inp.readline()
    if not _line:
        break
    _req = json.loads(_line)
    _pid = os.fork()
    if _pid == 0:
        import gc
        gc.freeze()  # CPU only: the parent's objects are never rescanned; young garbage still collected
        gc.set_threshold(20000, 50, 1000)
        for _p, _fl, _to in ((_req["out"], os.O_WRONLY | os.O_TRUNC, 1), (os.devnull, os.O_WRONLY, 2),
                             (os.devnull, os.O_RDONLY, 0)):
            _fd = os.open(_p, _fl)
            os.dup2(_fd, _to)
            os.close(_fd)
        try:
            sys.argv = ["-c", _req["cfg"], root, app]
            exec(compile(_E1_WORK_SRC, "<string>", "exec"), globals())
        finally:
            try:
                sys.stdout.flush()
            finally:
                os._exit(0)
    os.write(1, (json.dumps({"pid": _pid}) + "\n").encode())
    os.waitpid(_pid, 0)
    os.write(1, b'{"done": 1}\n')
"""


class _Server:
    def __init__(self):
        self.proc, self.asked, self.dead, self.buf = None, None, False, b""

    def _start(self, src_root, env):
        self.root = str(src_root)
        self.proc = subprocess.Popen([sys.executable, "-I", "-S", "-c", _E1_SERVER.replace(
            "_E1_WORK_SRC", repr(_E1_WORK)), "", self.root, str(Path(__file__).resolve().parent)],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, env=env)
        hello = self._line(CHILD_TIMEOUT_S)
        if not hello or not hello.get("ok"):
            raise RuntimeError("E1 server unavailable")
        self.asked = set(hello["asked"])

    def _line(self, timeout):
        import select
        import time
        deadline = time.monotonic() + timeout
        fd = self.proc.stdout.fileno()
        while b"\n" not in self.buf:
            left = deadline - time.monotonic()
            if left <= 0 or not select.select([fd], [], [], left)[0]:
                return None
            chunk = os.read(fd, 65536)
            if not chunk:
                raise RuntimeError("E1 server exited")
            self.buf += chunk
        line, self.buf = self.buf.split(b"\n", 1)
        return json.loads(line)

    def run(self, src_root, cfg, names, timeout, env):

        import tempfile
        import time
        if self.dead or not hasattr(os, "fork") or os.environ.get("RWX_E1_FORK", "1") != "1":
            return None
        try:
            if self.proc is None:
                self._start(src_root, env)
            if str(src_root) != self.root or names & self.asked:
                return None
            fo, out = tempfile.mkstemp(suffix=".out")
            os.close(fo)
            try:
                t0 = time.monotonic()
                self.proc.stdin.write((json.dumps({"cfg": cfg, "out": out}) + "\n").encode())
                self.proc.stdin.flush()
                pid = self._line(timeout)
                if pid is None:
                    raise RuntimeError("E1 server not answering")
                done = self._line(max(0.0, timeout - (time.monotonic() - t0)))
                if done is None:
                    try:
                        os.kill(pid["pid"], 9)
                    except OSError:
                        pass
                    if self._line(timeout) is None:
                        raise RuntimeError("E1 server stuck")
                    raise subprocess.TimeoutExpired("e1", timeout)
                with open(out, encoding="utf-8") as fh:
                    return fh.read()
            finally:
                os.unlink(out)
        except subprocess.TimeoutExpired:
            raise
        except Exception:
            self.close()
            self.dead = True
            return None

    def close(self):
        if self.proc is not None:
            try:
                self.proc.stdin.close()
                self.proc.wait(timeout=CHILD_TIMEOUT_S)
            except Exception:
                self.proc.kill()
                self.proc.wait()
            self.proc = None


_SERVER = _Server()


def close_server():
    _SERVER.close()


def _modname(rel):
    name = rel[:-3].replace("/", ".")
    is_pkg = name.endswith(".__init__")
    return (name[: -len(".__init__")] if is_pkg else name), is_pkg


def recompute(src_root, patched_files, work, timeout=CHILD_TIMEOUT_S, expect=None, fixtures=None):


    import tempfile
    mods = {}
    for rel, text in patched_files.items():
        name, is_pkg = _modname(rel)
        mods[name] = [text, is_pkg, str(Path(src_root) / rel).replace("\\", "/")]
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8") as fh:
        json.dump({"patched": mods, "work": work, "expect": expect or {}, "fixtures": fixtures or {}}, fh)
        tmp = fh.name
    try:
        env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
        out = _SERVER.run(src_root, tmp, set(mods), timeout, env)
        if out is not None:
            return json.loads(out.strip().splitlines()[-1])
        r = subprocess.run([sys.executable, "-I", "-S", "-c", _CHILD, tmp, str(src_root),
                            str(Path(__file__).resolve().parent)],
                           capture_output=True, text=True, timeout=timeout, env=env)
        return json.loads(r.stdout.strip().splitlines()[-1])
    except Exception:
        return None
    finally:
        os.unlink(tmp)




class Cutoff:
    def __init__(self, path, m=None):
        if m is None:
            with gzip.open(path, "rt", encoding="utf-8") as fh:
                m = json.load(fh)
        self.tests = {}
        for tid, d in m["tests"].items():
            self.tests[tid] = {
                "kind": d["kind"],
                "E": {f: set(v) for f, v in d["E"].items()},
                "Q": [{f: set(v) for f, v in q.items()} for q in d["Q"]],
                "fp": d["fp"],
            }

    def plan(self, tid, regions):


        d = self.tests.get(tid)
        if d is None:
            return None
        qs = set()
        for path, ranges in regions:
            ex = d["E"].get(path, ())
            for lo, hi in ranges:
                if any(lo <= ln <= hi for ln in ex):
                    return None
                hit = False
                for i, q in enumerate(d["Q"]):
                    if any(lo <= ln <= hi for ln in q.get(path, ())):
                        qs.add(i)
                        hit = True
                if not hit:
                    return None
        return sorted(qs)

    def droppable(self, src_root, patched_files, wants):


        work, plans = {}, {}
        for tid, regions in wants.items():
            p = self.plan(tid, regions)
            if p is None:
                continue
            plans[tid] = p
            work.setdefault(self.tests[tid]["kind"], set()).update(p)
        if not work:
            return {}
        expect = {t["kind"]: t["fp"] for t in self.tests.values()}
        got = recompute(src_root, patched_files, {k: {"idx": sorted(v)} for k, v in work.items()}, expect=expect)
        if not got:
            return {}
        out = {}
        for tid, p in plans.items():
            d = self.tests[tid]
            g = got.get(d["kind"], {})
            if all(g.get(str(i)) == d["fp"][i] for i in p):
                out[tid] = f"{len(p)} boundary fingerprints equal"
        return out
