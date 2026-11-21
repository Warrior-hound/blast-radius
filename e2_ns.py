"""E2 namespace fingerprint and diff (runs in a throwaway interpreter, PYTHONHASHSEED=0).

  python e2_ns.py build SRC OUT.pickle          fingerprint of the pinned tree (image build time)
  python e2_ns.py diff SRC FP.pickle CFG.json   import the patched modules (CFG: {"patched": {mod: [src,
                                                is_pkg, origin]}}), then every sqlglot module, and print
                                                one JSON line: {"changes": [[loc, keys|null], ...]} or
                                                {"error": ...}

Locations: G|module|name (module global), C|module:qualname|attr (class attribute). The value of a
location is fingerprinted deeply (containers, instances, closures, defaults; code objects without
line numbers). A class or function that lives at its own canonical location is referenced by name
elsewhere, and its own location carries its content. For dict / set values the per-key fingerprints
are kept too, so a diff can name the keys that changed (keys: list of key reprs, null = whole value).
"""
import enum
import hashlib
import importlib
import importlib.abc
import importlib.util
import json
import pickle
import pkgutil
import re
import sys
import types

SKIP_DUNDER = {"__dict__", "__weakref__", "__module__", "__qualname__", "__firstlineno__",
               "__static_attributes__", "__builtins__", "__cached__", "__file__", "__loader__", "__spec__",
               "__path__", "__package__", "__name__",
               "_abc_impl"}  # abc's per-class registry cache (C object), not a value the code reads


def _cname(c):
    return f"{getattr(c, '__module__', '?')}:{getattr(c, '__qualname__', '?')}"


def keyrep(k):
    t = type(k)
    if t in (str, int, bool, float) or k is None:
        return repr(k)
    if t is tuple:
        parts = [keyrep(x) for x in k]
        return None if None in parts else "(" + ",".join(parts) + ")"
    if isinstance(k, enum.Enum):
        return f"E:{_cname(type(k))}.{k.name}"
    if isinstance(k, type):
        return "T:" + _cname(k)
    return None


def _canonical(obj):
    """obj is reachable as module.qualname (so its own location is fingerprinted)."""
    mod = sys.modules.get(getattr(obj, "__module__", None) or "")
    qn = getattr(obj, "__qualname__", None)
    if mod is None or not qn or "<" in qn:
        return False
    o = mod
    for part in qn.split("."):
        o = o.__dict__.get(part) if isinstance(o, types.ModuleType) else vars(o).get(part) if isinstance(o, type) else None
        if o is None:
            return False
    return o is obj


def _code_sig(co):
    consts = []
    for c in co.co_consts:
        consts.append(("<code>", _code_sig(c)) if isinstance(c, types.CodeType) else _const(c))
    return (co.co_code, tuple(consts), co.co_names, co.co_varnames, co.co_freevars, co.co_cellvars,
            co.co_argcount, co.co_posonlyargcount, co.co_kwonlyargcount, co.co_flags,
            getattr(co, "co_exceptiontable", b""), co.co_name, co.co_qualname)


def _const(c):
    if isinstance(c, frozenset):
        return ("frozenset", tuple(sorted((repr(_const(e)) for e in c))))
    if isinstance(c, tuple):
        return ("tuple", tuple(_const(e) for e in c))
    return (type(c).__name__, repr(c))


class FP:
    def __init__(self):
        self.memo = {}
        self.busy = set()
        self.keep = []
        self.opq = set()  # ids of values whose fingerprint contains an opaque part
        self.stack = [False]

    def _opaque(self):
        self.stack[-1] = True

    def h(self, v):
        i = id(v)
        r = self.memo.get(i)
        if r is not None:
            if i in self.opq:
                self._opaque()
            return r
        if i in self.busy:
            return "cycle:" + type(v).__name__
        self.busy.add(i)
        self.stack.append(False)
        try:
            c = self._canon(v)
        finally:
            self.busy.discard(i)
            op = self.stack.pop()
        if op:
            self.opq.add(i)
            self._opaque()
        r = hashlib.blake2b(repr(c).encode("utf-8", "backslashreplace"), digest_size=10).hexdigest()
        self.memo[i] = r
        self.keep.append(v)
        return r

    def _canon(self, v):
        h = self.h
        t = type(v)
        if v is None or t in (bool, int, float, complex, str, bytes):
            return (t.__name__, repr(v))
        if t in (tuple, list):
            return (t.__name__, [h(x) for x in v])
        if isinstance(v, enum.Enum):
            return ("E", _cname(type(v)), v.name)
        if isinstance(v, dict):
            # ordered: entry order is semantic (arg_types fill positional arguments). Dicts built from
            # sets of id-hashed objects differ between clean imports: the build marks those
            # locations unstable and compares them order-insensitively (see unordered)
            return (_cname(t), [(h(k), h(x)) for k, x in v.items()], h(getattr(v, "default_factory", None)))
        if isinstance(v, (set, frozenset)):
            return (t.__name__, sorted(h(x) for x in v))
        if isinstance(v, (type({}.keys()), type({}.values()), type({}.items()))):
            return (t.__name__, [h(x) for x in v])
        if isinstance(v, types.ModuleType):
            return ("Mod", v.__name__)
        if isinstance(v, type):
            if not (v.__module__ or "").startswith("sqlglot") or _canonical(v):
                return ("T", _cname(v))
            return ("TD", _cname(v), [b.__qualname__ for b in v.__mro__],
                    [(k, h(x)) for k, x in vars(v).items() if k not in SKIP_DUNDER])
        if isinstance(v, types.FunctionType):
            if _canonical(v):
                return ("F", _cname(v))
            return self._fn(v)
        return self._rest(v, t)

    def _fn(self, v):
        h = self.h
        if True:
            cells = []
            for c in v.__closure__ or ():
                try:
                    cells.append(h(c.cell_contents))
                except ValueError:
                    cells.append("empty")
            return ("Fn", _code_sig(v.__code__), h(v.__defaults__), h(v.__kwdefaults__), cells,
                    [(k, h(x)) for k, x in vars(v).items() if k != "__wrapped__"], h(getattr(v, "__wrapped__", None)))

    def _rest(self, v, t):
        h = self.h
        if isinstance(v, types.MethodType):
            return ("BM", h(v.__func__), h(v.__self__))
        if isinstance(v, (types.BuiltinFunctionType, types.BuiltinMethodType)):
            s = getattr(v, "__self__", None)
            return ("B", getattr(v, "__module__", None), v.__qualname__,
                    None if s is None or isinstance(s, types.ModuleType) else h(s))
        if isinstance(v, (staticmethod, classmethod)):
            return (t.__name__, h(v.__func__))
        if isinstance(v, property):
            return ("P", h(v.fget), h(v.fset), h(v.fdel))
        if t.__name__ == "partial":
            return ("partial", h(v.func), h(v.args), h(v.keywords))
        if isinstance(v, re.Pattern):
            return ("re", v.pattern, v.flags)
        if isinstance(v, types.CodeType):
            return ("code", _code_sig(v))
        state = []
        d = getattr(v, "__dict__", None)
        if isinstance(d, dict):
            state += [(k, h(x)) for k, x in d.items()]
        for k in getattr(t, "__slots__", ()) if isinstance(getattr(t, "__slots__", ()), (tuple, list)) else ():
            try:
                state.append((k, h(getattr(v, k))))
            except AttributeError:
                pass
        if not state and (t.__module__ or "").startswith(("_thread", "threading", "itertools", "weakref", "_weakref")):
            return ("X", _cname(t))
        if isinstance(v, types.MappingProxyType):
            return ("MP", sorted((h(k), h(x)) for k, x in v.items()))
        if not state:
            # no __dict__ / __slots__ state: a C object (date, Decimal, range, deque, bytearray, ...)
            # keeps its value inside; take it from the pickle protocol, else mark it opaque
            try:
                red = v.__reduce_ex__(4)
            except Exception:  # noqa: BLE001
                red = None
            if isinstance(red, str):  # pickled by reference (TypeVar, singletons): its global name
                return ("RG", _cname(t), getattr(v, "__module__", None), red)
            if isinstance(red, tuple) and len(red) >= 2:
                parts = []
                for x in red[1:]:
                    if hasattr(x, "__next__"):
                        x = list(x)
                    parts.append(h(x))
                return ("R", _cname(t), h(red[0]), parts)
            self._opaque()
            return ("OPAQUE", _cname(t))
        return ("O", _cname(t), state)

    def value(self, v, top=False):
        """Fingerprint of a location's value; self.last_opaque tells whether part of it is opaque."""
        self.stack = [False]
        if top and isinstance(v, types.FunctionType):
            c = self._fn(v)
            r = hashlib.blake2b(repr(c).encode("utf-8", "backslashreplace"), digest_size=10).hexdigest()
        else:
            r = self.h(v)
        self.last_opaque = self.stack[0]
        return r


def _span(co):
    lines = [ln for _, _, ln in co.co_lines() if ln is not None] + [co.co_firstlineno]
    for c in co.co_consts:
        if isinstance(c, types.CodeType):
            lines += list(_span(c))
    return min(lines), max(lines)


def _codehash(co):
    return hashlib.blake2b(repr(_code_sig(co)).encode("utf-8", "backslashreplace"), digest_size=10).hexdigest()


def _meta(v):
    """For function-like values: (file, first line, last line) of their code (old tree)."""
    fs = []
    if isinstance(v, (staticmethod, classmethod)):
        v = v.__func__
    if isinstance(v, property):
        fs = [f for f in (v.fget, v.fset, v.fdel) if isinstance(f, types.FunctionType)]
    elif isinstance(v, types.FunctionType):
        fs = [v]
    out = []
    for f in fs:
        while isinstance(getattr(f, "__wrapped__", None), types.FunctionType):
            out.append((f.__code__.co_filename,) + _span(f.__code__) + (_codehash(f.__code__),))
            f = f.__wrapped__
        out.append((f.__code__.co_filename,) + _span(f.__code__) + (_codehash(f.__code__),))
    return out or None


STRVALS = {}  # dict location -> {keyrep: value} for its str values (lazy-import tables name modules)


def _keys(fp, v, loc=None):
    # only the exact types the tracer instruments (subclasses such as defaultdict are not)
    if type(v) is dict:
        out = {}
        sv = {}
        for k, x in v.items():
            r = keyrep(k)
            if r is None:
                return None
            out[r] = fp.h(x)
            if type(x) is str:
                sv[r] = x
        if sv and loc is not None:
            STRVALS[loc] = sv
        return out
    if type(v) in (set, frozenset):
        out = {}
        for k in v:
            r = keyrep(k)
            if r is None:
                return None
            out[r] = "1"
        return out
    return None


CLASSES = {}  # canonical class name -> class (filled by fingerprint)
OPAQUE = set()  # locations whose value has a part the fingerprint cannot see into


def fingerprint():
    """{loc: (hash, keys or None, meta)} for every sqlglot module currently imported."""
    fp = FP()
    out = {}
    seen = set()

    def cls(c, cn):
        if id(c) in seen:
            return
        seen.add(id(c))
        CLASSES[cn] = c
        for n, v in list(vars(c).items()):
            if n in SKIP_DUNDER:
                continue
            loc = f"C|{cn}|{n}"
            if isinstance(v, type) and _canonical(v) and _cname(v) == f"{cn}.{n}":
                cls(v, _cname(v))
                out[loc] = ("T:" + _cname(v), None, None)
                continue
            hv = fp.value(v, top=True)
            if fp.last_opaque:
                OPAQUE.add(loc)
            out[loc] = (hv, _keys(fp, v, loc), _meta(v))

    for name in sorted(n for n in sys.modules if n.startswith("sqlglot")):
        m = sys.modules[name]
        if not isinstance(m, types.ModuleType):
            continue
        for n, v in list(vars(m).items()):
            if n in SKIP_DUNDER:
                continue
            loc = f"G|{name}|{n}"
            if isinstance(v, type) and getattr(v, "__module__", None) == name and _canonical(v) and v.__qualname__ == n:
                cls(v, _cname(v))
                out[loc] = ("T:" + _cname(v), None, None)
                continue
            hv = fp.value(v, top=True)
            if fp.last_opaque:
                OPAQUE.add(loc)
            out[loc] = (hv, _keys(fp, v, loc), _meta(v))
    return out


def _lookup(loc):
    kind, owner, n = loc.split("|", 2)
    if kind == "G":
        return vars(sys.modules[owner])[n]
    return vars(CLASSES[owner])[n]


def unordered(loc):
    """Order-insensitive fingerprint of a location whose value differs between clean imports
    (tuples / lists built by iterating a set of id-hashed objects)."""
    fp = FP()
    v = _lookup(loc)
    if type(v) in (tuple, list):
        return repr(sorted(fp.h(x) for x in v))
    if isinstance(v, dict):
        return repr(sorted((fp.h(k), fp.h(x)) for k, x in v.items()))
    return fp.value(v, top=True)


def import_all(src):
    sys.path.insert(0, src)
    import sqlglot
    root = sqlglot.__path__[0]
    failed = []
    for m in pkgutil.walk_packages([root], "sqlglot.", onerror=lambda n: failed.append(n)):
        try:
            importlib.import_module(m.name)
        except BaseException:
            failed.append(m.name)
    return failed


class Finder(importlib.abc.MetaPathFinder, importlib.abc.Loader):
    def __init__(self, patched):
        self.patched = patched

    def find_spec(self, name, path, target=None):
        if name in self.patched:
            return importlib.util.spec_from_loader(name, self, origin=self.patched[name][2], is_package=self.patched[name][1])
        return None

    def create_module(self, spec):
        return None

    def exec_module(self, module):
        src, is_pkg, origin = self.patched[module.__name__]
        if is_pkg:
            module.__path__ = [origin.rsplit("/", 1)[0]]
        module.__file__ = origin
        exec(compile(src, origin, "exec"), module.__dict__)


def diff(old, new):
    changes = []
    for loc in sorted(set(old) | set(new)):
        a, b = old.get(loc), new.get(loc)
        if a is not None and b is not None and a[0] == b[0]:
            continue
        keys = None
        if a is not None and b is not None and a[1] is not None and b[1] is not None:
            ka, kb = a[1], b[1]
            keys = sorted(k for k in set(ka) | set(kb) if ka.get(k) != kb.get(k))
        override = None
        if a is None and loc.startswith("C|"):
            # an added class attribute: did lookups through this class find it on a base before?
            _, cn, n = loc.split("|", 2)
            c = CLASSES.get(cn)
            # the first base that defines it (its location must be traced for the readers to be known)
            override = next((_cname(k) for k in c.__mro__[1:] if n in vars(k)), None) if c is not None else None
        changes.append([loc, keys, "added" if a is None else "removed" if b is None else "changed",
                        a[2] if a is not None else None, b[2] if b is not None else None,
                        a[0] if a is not None else None, b[0] if b is not None else None, override])
    return changes


def main():
    # the suite runs with unittest / pytest imported, and import-time code depends on it
    # (sqlglot.expressions.core.UNITTEST turns on argument validation): import like the tests do
    import unittest  # noqa: F401
    cmd, src = sys.argv[1], sys.argv[2]
    sys.setrecursionlimit(20000)
    if cmd == "build":
        failed = import_all(src)
        fpr = fingerprint()
        with open(sys.argv[3], "wb") as fh:
            pickle.dump({"fp": fpr, "failed": sorted(failed)}, fh, protocol=pickle.HIGHEST_PROTOCOL)
        # locations that change between two clean imports: keep an order-insensitive fingerprint
        import subprocess
        import tempfile
        cfg = tempfile.NamedTemporaryFile("w", suffix=".json", delete=False)
        cfg.write('{"patched": {}}')
        cfg.close()
        unstable = set()
        for _ in range(4):
            r = subprocess.run([sys.executable, "-I", "-S", __file__, "diff", src, sys.argv[3], cfg.name],
                               capture_output=True, text=True, timeout=300)
            unstable |= {c[0] for c in json.loads(r.stdout.strip().splitlines()[-1])["changes"]}
        fpr_u = {loc: unordered(loc) for loc in sorted(unstable)}
        with open(sys.argv[3], "wb") as fh:
            pickle.dump({"fp": fpr, "failed": sorted(failed), "unstable": fpr_u, "strvals": dict(STRVALS)}, fh,
                        protocol=pickle.HIGHEST_PROTOCOL)
        print(json.dumps({"unstable": fpr_u}))
        if len(sys.argv) > 4:  # canonical class names (the selector's MRO bookkeeping needs them)
            with open(sys.argv[4], "w", encoding="utf-8") as fh:
                json.dump(sorted(CLASSES), fh)
        print(json.dumps({"locations": len(fpr), "failed": failed}))
        return
    try:
        with open(sys.argv[3], "rb") as fh:
            base = pickle.load(fh)
        cfg = json.load(open(sys.argv[4], encoding="utf-8"))
        sys.meta_path.insert(0, Finder(cfg["patched"]))
        failed = import_all(src)
        if sorted(failed) != base["failed"]:
            print(json.dumps({"error": f"import failures differ: {sorted(set(failed) ^ set(base['failed']))}"}))
            return
        changes = diff(base["fp"], fingerprint())
        uns = base.get("unstable", {})
        changes = [c for c in changes if not (c[0] in uns and c[2] == "changed" and unordered(c[0]) == uns[c[0]])]
        pm = tuple(cfg["patched"])
        opaque = sorted(loc for loc in OPAQUE if loc.split("|")[1].split(":")[0] in pm)
        # str values of the changed keys, old and new: a table of module names drives lazy imports
        bsv = base.get("strvals", {})
        strvals = {}
        for c in changes:
            if c[1]:
                vals = {bsv.get(c[0], {}).get(k) for k in c[1]} | {STRVALS.get(c[0], {}).get(k) for k in c[1]}
                vals.discard(None)
                if vals:
                    strvals[c[0]] = sorted(vals)
        print(json.dumps({"changes": changes, "opaque": opaque, "strvals": strvals}))
    except BaseException as e:  # noqa: BLE001
        print(json.dumps({"error": f"{type(e).__name__}: {e}"}))


if __name__ == "__main__":
    main()
