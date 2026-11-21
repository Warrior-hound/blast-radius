"""E1: stage-boundary early cutoff for sqlglot's TPC executor tests.

test_execute_tpcds / test_execute_tpch / test_optimized_tpch consume sqlglot in two phases per query:
  C (compile): parse_one -> pickle round trip -> find_tables -> ensure_schema -> optimize -> Plan,
               plus transpile(write="duckdb") for the reference result,
  E (execute): everything else (Table loading, ensure_tables, PythonExecutor, generated Python).
Only the C outputs cross into E: the Plan DAG, the table names, schema.supported_table_args and the
duckdb strings. If every changed statement that brought such a test in ran only in C (per the offline
phase map), and the C outputs recomputed with the patched sources equal the pinned ones, E runs the
same code on the same inputs, so the test's outcome cannot change (early cutoff, by determinism).

The phase map and pinned fingerprints are built offline by solution/rwx/lab/e1_lab.py.
Anything unexpected (missing map, child error, timeout, mismatch) keeps the test.
"""
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
    """(name, value) pairs of an instance, read from slots and __dict__ (no methods called).
    Expression._hash is skipped: it caches a hash-seed dependent value."""
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
    """Token for a leaf value, or None for a container/instance."""
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
    """(open token, children) of a container/instance."""
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
    """History-independent ordering key for a set member: its base key refined by the keys of the
    members of its own set-valued fields (a few rounds of Weisfeiler-Lehman style refinement)."""
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
    """A dump of what o reaches without following `parent` links or entering nested sets (those
    contribute their members' shallow keys)."""
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
    """Members ordered by their shallow key; members whose shallow keys collide by the full key."""
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
    """(kind, header, slot names) per type, cached: kinds 0 atom, 1 list/tuple, 2 dict, 3 set, 4 object."""
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
    """Deterministic dump of the object graph reachable from root, read directly from instance
    slots/__dict__ (never through sqlglot's own methods, which may be the patched code). Shared
    objects and cycles become back-references, so identity structure (e.g. parent links) is kept.
    Set members are visited in an order that depends only on the graph, not on hash seeds.
    Prefix encoding: every container token carries its arity, so no closing tokens are needed.
    Expression._hash is skipped: it caches a hash-seed dependent value."""
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


# ------------------------------------------------------------------ the C-phase computation

FIXTURE = {"tpcds": ("optimizer/tpc-ds/tpc-ds.sql", "TPCDS_SCHEMA"),
           "tpch": ("optimizer/tpc-h/tpc-h.sql", "TPCH_SCHEMA"),
           "opt_tpch": ("optimizer/tpc-h/tpc-h.sql", None)}


def boundary(kind, sql, meta, optimized, schema_dict):
    """The values the test's E phase (or assertion) receives from sqlglot for one query."""
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
        # what the test's parent process does with every query; only failures are observable
        # for the ones it does not execute, since mp_execute then returns None
        e = pickle.loads(pickle.dumps(parse_one(sql)))
        parts.append("parsed")
        if meta.get("execute"):
            parts.append("tables:" + json.dumps(sorted(t.name for t in find_tables(e))))
            schema = ensure_schema(schema_dict, dialect=None)
            plan = Plan(optimize(e, schema, leave_tables_isolated=True, dialect=None))
            parts += canon(plan)
            parts += canon(schema.supported_table_args)
            parts.append("D" + transpile(sql, write="duckdb")[0])
    except Exception as ex:  # noqa: BLE001  (the exception type is part of the boundary)
        parts.append(f"EXC {type(ex).__module__}.{type(ex).__qualname__}")
    return digest(parts)


def load_queries(kind):
    from tests import helpers
    fname, schema_name = FIXTURE[kind]
    qs = list(helpers.load_sql_fixture_pairs(fname))
    schema = getattr(helpers, schema_name) if schema_name else None
    return qs, schema


_CHILD = r"""
import importlib, importlib.abc, importlib.util, json, sys
cfg = json.load(open(sys.argv[1], encoding="utf-8"))
root, app = sys.argv[2], sys.argv[3]
patched = cfg["patched"]
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
sys.setrecursionlimit(100000)
sys.path.insert(0, root)
sys.meta_path.insert(0, Finder())
sys.path.insert(0, app)
import e1_cutoff as E
out = {}
for kind, idx in cfg["work"].items():
    qs, schema = E.load_queries(kind)
    exp = cfg.get("expect", {}).get(kind)
    out[kind] = {}
    for i in idx:
        d = out[kind][str(i)] = E.boundary(kind, qs[i][1], qs[i][0], qs[i][2], schema)
        if exp is not None and d != exp[i]:
            break  # one difference settles it: keep the test
print(json.dumps(out))
"""


def _modname(rel):
    name = rel[:-3].replace("/", ".")
    is_pkg = name.endswith(".__init__")
    return (name[: -len(".__init__")] if is_pkg else name), is_pkg


def recompute(src_root, patched_files, work, timeout=CHILD_TIMEOUT_S, expect=None):
    """Boundary digests under the patched sources, in an isolated interpreter.
    patched_files: {rel path: new text}; work: {kind: [query index]}. None on any failure."""
    import tempfile
    mods = {}
    for rel, text in patched_files.items():
        name, is_pkg = _modname(rel)
        mods[name] = [text, is_pkg, str(Path(src_root) / rel).replace("\\", "/")]
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8") as fh:
        json.dump({"patched": mods, "work": work, "expect": expect or {}}, fh)
        tmp = fh.name
    try:
        env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")  # -I: random hash seed, digests must not depend on it
        r = subprocess.run([sys.executable, "-I", "-S", "-c", _CHILD, tmp, str(src_root),
                            str(Path(__file__).resolve().parent)],
                           capture_output=True, text=True, timeout=timeout, env=env)
        return json.loads(r.stdout.strip().splitlines()[-1])
    except Exception:  # noqa: BLE001
        return None
    finally:
        os.unlink(tmp)


# ------------------------------------------------------------------ the runtime rule

class Cutoff:
    def __init__(self, path):
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
        """regions: [(old path, [(lo, hi), ...])] that brought test tid in. Returns the query
        indices to recompute, or None when the rule cannot apply."""
        d = self.tests.get(tid)
        if d is None:
            return None
        qs = set()
        for path, ranges in regions:
            ex = d["E"].get(path, ())
            hit_any = False
            for lo, hi in ranges:
                if any(lo <= ln <= hi for ln in ex):
                    return None  # the changed statement runs in the execute phase
                for i, q in enumerate(d["Q"]):
                    if any(lo <= ln <= hi for ln in q.get(path, ())):
                        qs.add(i)
                        hit_any = True
            if not hit_any:
                return None  # the map says the test ran it, the phase trace did not: be safe
        return sorted(qs)

    def droppable(self, src_root, patched_files, wants):
        """wants: {test id: [(path, ranges)]}. Returns ({test id: reason}) for tests proven
        unaffected; every other test is kept."""
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
        got = recompute(src_root, patched_files, {k: sorted(v) for k, v in work.items()}, expect=expect)
        if not got:
            return {}
        out = {}
        for tid, p in plans.items():
            d = self.tests[tid]
            g = got.get(d["kind"], {})
            if all(g.get(str(i)) == d["fp"][i] for i in p):
                out[tid] = f"{len(p)} boundary fingerprints equal"
        return out
