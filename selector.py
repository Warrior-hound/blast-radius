















import ast
import gc
import gzip
import json
import math
import os
import re
import sys
import threading
import time
import types
from pathlib import Path

APP = Path(__file__).resolve().parent
DATA = Path(os.environ.get("RWX_DATA", "/data"))
SRC = Path(os.environ.get("RWX_SRC", APP / "sqlglot"))
MAP = Path(os.environ.get("RWX_MAP", APP / "map.json.gz"))
MAX_WORKERS = 8

IMPORT_TIME_RULE = os.environ.get("RWX_IMPORT_TIME_RULE", "0") == "1"


FRAME_DIFF = os.environ.get("RWX_FRAME_DIFF", "1") == "1"
E1 = os.environ.get("RWX_E1", "1") == "1"
WORKER_COST_MS = 2000
PROBE_TIMEOUT_S = 10


RUN_LIMIT_S = float(os.environ.get("RWX_RUN_LIMIT_S", "180"))




SAFE_FRACTION = 0.6


E1_BUDGET_S = float(os.environ.get("RWX_E1_BUDGET_S", 0.25 * RUN_LIMIT_S))



E1S = os.environ.get("RWX_E1S", "1") == "1"
E1S_SCOPE = os.environ.get("RWX_E1S_SCOPE", "0") == "1"

E1S_BUDGET_S = float(os.environ.get("RWX_E1S_BUDGET_S", 0.15 * RUN_LIMIT_S))
E1S_DIFF_MS = 1600
E1S_CHILD_MS = 200
E1S_KIND_MS = {"tpcds": 3900, "tpch": 150, "opt_tpch": 150}
E1S_FIXTURE_MS = 100
E1S_FIXTURES = {"tests/fixtures/" + f: f for f in ("optimizer/tpc-ds/tpc-ds.sql", "optimizer/tpc-h/tpc-h.sql")}



VERIFY = os.environ.get("RWX_VERIFY", "1") == "1"
VERIFY_P0 = 0.3
VERIFY_START_MS = 60
VERIFY_TEST_MS = 20
VERIFY_BUDGET_MS = 8000
VERIFY_BOOT_MS = 1500


VERIFY_NEVER = ("test_generator_memory", "test_execute_tpcds")
WATCHDOG_FRACTION = 0.7



LAZY = os.environ.get("RWX_LAZY", "1") == "1"
STATIC_IMPORT = os.environ.get("RWX_STATIC_IMPORT", "0") == "1"

CONFIG_FILES = {"conftest.py", "tests/conftest.py", "setup.cfg", "pytest.ini", "tox.ini", "pyproject.toml"}




E2 = os.environ.get("RWX_E2", "0") == "1"



E2_PRUNE = os.environ.get("RWX_E2_PRUNE", "1") == "1"

E2_STRICT_IMPORTS = os.environ.get("RWX_E2_STRICT_IMPORTS", "0") == "1"
L5 = os.environ.get("RWX_L5", "1") == "1"
L2 = os.environ.get("RWX_L2", "1") == "1"
E2_MAP = Path(os.environ.get("RWX_E2_MAP", APP / "e2map.json.gz"))
E2_TIMEOUT_S = 20
E2_COST_MS = 1600



ORDER = os.environ.get("RWX_ORDER", "1") == "1"
ORDER_STATE = Path(os.environ.get("RWX_ORDER_STATE", APP / "cache" / "order_state.json"))
E2_FP = Path(os.environ.get("RWX_E2_FP", APP / "cache" / "e2fp.pickle"))
E2_CANON = E2_FP.with_suffix(".canon.json")






_PARSED = {}
_PARSED_MAX = 8


def _parse(text):
    t = _PARSED.pop(text, None)
    if t is None:
        t = ast.parse(text)
        if len(_PARSED) >= _PARSED_MAX:
            del _PARSED[next(iter(_PARSED))]
    _PARSED[text] = t
    return t


def _dump_field(v):
    if isinstance(v, ast.AST):
        return ast.dump(v)
    if isinstance(v, list):
        return [ast.dump(x) if isinstance(x, ast.AST) else repr(x) for x in v]
    return repr(v)


def _header(st):




    head, dflt = [], None
    for f, v in ast.iter_fields(st):
        if f == "body":
            continue
        if f == "args":
            head.append((f, tuple((g, _dump_field(w)) for g, w in ast.iter_fields(v) if g not in ("defaults", "kw_defaults"))))
            dflt = (_dump_field(v.defaults), _dump_field(v.kw_defaults))
        else:
            head.append((f, _dump_field(v)))
    return ("def", type(st).__name__, tuple(head), dflt)


def _is_stdlib(name):
    top = name.split(".")[0]
    return top in sys.builtin_module_names or top in getattr(sys, "stdlib_module_names", ())


def _loading_imports(tree, path):



    mod = path[:-3].replace("/", ".")
    is_pkg = mod.endswith(".__init__")
    if is_pkg:
        mod = mod[: -len(".__init__")]
    pkg = mod if is_pkg else mod.rpartition(".")[0]
    parts = mod.split(".")
    loaded = {".".join(parts[:i]) for i in range(1, len(parts) + (1 if is_pkg else 0))}
    seq = []

    def chain(name):
        p = name.split(".")
        return [".".join(p[:i]) for i in range(1, len(p) + 1)]

    def visit(stmts):
        for st in stmts:
            if isinstance(st, ast.Import):
                for al in st.names:
                    mods = chain(al.name)
                    if any(m not in loaded and not _is_stdlib(m) for m in mods):
                        seq.append(("import", al.name, al.asname))
                    loaded.update(mods)
            elif isinstance(st, ast.ImportFrom):
                if st.level:
                    b = pkg.split(".") if pkg else []
                    b = b[: len(b) - (st.level - 1)] if st.level > 1 else b
                    base = ".".join(b + ([st.module] if st.module else []))
                else:
                    base = st.module or ""
                for al in st.names:
                    mods = chain(base) if base else []
                    if al.name != "*" and _mod_file(f"{base}.{al.name}") is not None:
                        mods.append(f"{base}.{al.name}")
                    if any(m not in loaded and not _is_stdlib(m) for m in mods):
                        seq.append(("from", st.module, st.level, al.name))
                    loaded.update(mods)
            elif isinstance(st, ast.ClassDef):
                visit(st.body)
            elif isinstance(st, (ast.If, ast.Try, ast.With)) or (hasattr(ast, "TryStar") and isinstance(st, ast.TryStar)):
                for blk in ("body", "orelse", "finalbody"):
                    visit(getattr(st, blk, []))
                for hd in getattr(st, "handlers", []):
                    visit(hd.body)
    visit(tree.body)
    return seq


def _scope_bindings(body):


    out = {}

    def add(k, v):
        out.setdefault(k, []).append(v)

    def walk(stmts, first):
        for i, st in enumerate(stmts):
            if first and i == 0 and isinstance(st, ast.Expr) and isinstance(st.value, ast.Constant)                     and isinstance(st.value.value, str):
                add("__doc__", ast.dump(st))
            elif isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):


                add(("def", st.name), _header(st))
            elif isinstance(st, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
                tg = st.targets if isinstance(st, ast.Assign) else [st.target]
                names = [n.id for t in tg for n in ast.walk(t) if isinstance(n, ast.Name)]
                if not names or any(not isinstance(t, (ast.Name, ast.Tuple, ast.List)) for t in tg):
                    add(None, ast.dump(st))
                for n in names:
                    add(n, ast.dump(st))
            elif isinstance(st, ast.Import):
                for al in st.names:
                    add(al.asname or al.name.split(".")[0], ("import", al.name, al.asname))
            elif isinstance(st, ast.ImportFrom):
                for al in st.names:
                    add(al.asname or al.name, ("from", st.module, st.level, al.name))
            elif isinstance(st, (ast.If, ast.Try)) or (hasattr(ast, "TryStar") and isinstance(st, ast.TryStar)):
                add(None, ("test", ast.dump(getattr(st, "test", ast.Constant(None)))))
                for blk in ("body", "orelse", "finalbody"):
                    walk(getattr(st, blk, []), False)
                for hd in getattr(st, "handlers", []):
                    walk(hd.body, False)
            elif isinstance(st, ast.Pass):
                continue
            else:
                add(None, ast.dump(st))
    walk(body, True)
    return out


_E2_DEFS = {}



_E2_UNMODELED = {}



_E2_DELS = {}


def _plain_deletion(node):
    if not isinstance(node, ast.FunctionDef) or node.decorator_list:
        return False
    if node.name.startswith("__") and node.name.endswith("__"):
        return False
    todo = list(node.body)
    while todo:
        n = todo.pop()
        if isinstance(n, (ast.Yield, ast.YieldFrom, ast.Await)):
            return False
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef)):
            continue
        todo.extend(ast.iter_child_nodes(n))
    return True


def _scope_defs(body):

    out = {}
    for st in body:
        if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            out.setdefault(st.name, []).append(st)
        elif isinstance(st, (ast.If, ast.Try)) or (hasattr(ast, "TryStar") and isinstance(st, ast.TryStar)):
            for blk in ("body", "orelse", "finalbody"):
                for k, v in _scope_defs(getattr(st, blk, [])).items():
                    out.setdefault(k, []).extend(v)
            for hd in getattr(st, "handlers", []):
                for k, v in _scope_defs(hd.body).items():
                    out.setdefault(k, []).extend(v)
    return out


def _ref_index(root=None):





    root = Path(root or SRC)
    trees = {}
    for base in ("sqlglot", "tests"):
        for p in (root / base).rglob("*.py"):
            try:
                trees[p.relative_to(root).as_posix()] = ast.parse(p.read_text(encoding="utf-8"))
            except (SyntaxError, ValueError, OSError):
                trees[p.relative_to(root).as_posix()] = None
    names = set()
    for rel, tree in trees.items():
        if rel.startswith("sqlglot/") and tree is not None:
            names |= {n.name for n in ast.walk(tree) if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))}
    out = {"*unparsed": [rel for rel, t in trees.items() if t is None]}

    def add(name, rel, node, in_func):
        out.setdefault(name, []).append([rel, node.lineno, getattr(node, "end_lineno", None) or node.lineno, in_func])

    for rel, tree in sorted(trees.items()):
        if tree is None:
            continue
        callees = {id(n.func) for n in ast.walk(tree) if isinstance(n, ast.Call)}
        todo = [(tree, False)]
        while todo:
            node, in_func = todo.pop()
            for ch in ast.iter_child_nodes(node):
                f = in_func or isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda))
                if isinstance(ch, ast.Name) and ch.id in names and id(ch) not in callees:
                    add(ch.id, rel, ch, f)
                elif isinstance(ch, ast.Attribute) and ch.attr in names and id(ch) not in callees:
                    add(ch.attr, rel, ch, f)
                elif isinstance(ch, ast.alias):
                    for nm in {ch.name.rsplit(".", 1)[-1], ch.asname}:
                        if nm in names:
                            add(nm, rel, node, f)
                elif isinstance(ch, ast.Constant) and isinstance(ch.value, str) and len(ch.value) < 200:
                    nm = ch.value.rsplit(".", 1)[-1]
                    if nm in names:
                        add(nm, rel, ch, f)
                todo.append((ch, f))
    return out


def e2_expected(path, old_text, new_text):



    try:
        to, tn = _parse(old_text), _parse(new_text)
    except (SyntaxError, ValueError):
        return None
    mod = path[:-3].replace("/", ".")
    if mod.endswith(".__init__"):
        mod = mod[: -len(".__init__")]
    exact, prefixes = set(), set()
    defs = _E2_DEFS[path] = set()
    _E2_UNMODELED[path] = False
    dels = _E2_DELS[path] = {}

    def classes(tree):
        out = {}

        def walk(body, pre):
            for st in body:
                if isinstance(st, ast.ClassDef):
                    q = pre + st.name
                    out[q] = st
                    walk(st.body, q + ".")
                elif isinstance(st, (ast.If, ast.Try)):
                    walk(st.body, pre)
                    walk(getattr(st, "orelse", []), pre)
        walk(tree.body, "")
        return out

    class Unmodeled(Exception):
        pass

    def compare(bo, bn, loc_of, prefix):
        a, b = _scope_bindings(bo), _scope_bindings(bn)
        for k in set(a) | set(b):
            if a.get(k) == b.get(k):
                continue
            va, vb = a.get(k, []), b.get(k, [])
            if E2_STRICT_IMPORTS and any(isinstance(v, tuple) and v[0] in ("import", "from") for v in va + vb):
                raise Unmodeled
            if isinstance(k, tuple) and va and vb:
                if E2_STRICT_IMPORTS or [h[:3] for h in va] != [h[:3] for h in vb]:


                    raise Unmodeled
                exact.add(loc_of(k[1]))
                continue
            if k is None:
                prefixes.add(prefix)
            elif isinstance(k, tuple):
                exact.add(loc_of(k[1]))
                defs.add(loc_of(k[1]))
                old_defs = _scope_defs(bo).get(k[1], [])
                if (k in a and k not in b and k[1] not in b and len(old_defs) == 1
                        and _plain_deletion(old_defs[0])):
                    n = old_defs[0]


                    dels[loc_of(k[1])] = (k[1], n.body[0].lineno, n.end_lineno)
            else:
                exact.add(loc_of(k))
    try:
        if _loading_imports(to, path) != _loading_imports(tn, path):



            raise Unmodeled
        compare(to.body, tn.body, lambda n: f"G|{mod}|{n}", f"G|{mod}|")
        co, cn = classes(to), classes(tn)
        for q in set(co) & set(cn):
            compare(co[q].body, cn[q].body, lambda n, q=q: f"C|{mod}:{q}|{n}", f"C|{mod}:{q}|")
        for q in set(co) - set(cn):
            defs.add(f"C|{mod}:{q}|*")
    except Unmodeled:
        _E2_UNMODELED[path] = True
        return set(), {f"G|{mod}|"}
    return exact, prefixes


_ASSERT_RUNS = ("assertRaises", "assertWarns", "assertLogs", "assertNoLogs")


def _assert_names():
    import unittest
    import unittest.mock
    tc = {n for n in dir(unittest.TestCase) if n.startswith("assert") and not n.startswith(_ASSERT_RUNS)}
    mk = {n for n in dir(unittest.mock.NonCallableMock) if n.startswith("assert_")}
    return tc, mk


def _pure_arg(n):


    if isinstance(n, ast.Starred):
        n = n.value
    if isinstance(n, (ast.Name, ast.Constant)):
        return True
    if isinstance(n, ast.Attribute):
        return _pure_arg(n.value)
    if isinstance(n, ast.Subscript):
        return _pure_arg(n.value) and _pure_arg(n.slice)
    if isinstance(n, (ast.Tuple, ast.List, ast.Set)):
        return all(_pure_arg(e) for e in n.elts)
    if isinstance(n, ast.Dict):
        return all(k is None or _pure_arg(k) for k in n.keys) and all(_pure_arg(v) for v in n.values)
    if isinstance(n, ast.UnaryOp):
        return _pure_arg(n.operand)
    return False


def assertion_deletions(old_text, new_text, helper_defs):






    import difflib
    try:
        to, tn = ast.parse(old_text), ast.parse(new_text)
    except (SyntaxError, ValueError):
        return 0
    ol, nl = old_text.splitlines(), new_text.splitlines()
    gone = set()
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, ol, nl, autojunk=False).get_opcodes():
        if tag == "equal":
            continue
        if tag != "delete":
            return 0
        gone |= set(range(i1 + 1, i2 + 1))
    if not gone:
        return 0
    if "*" in helper_defs:
        return 0
    tc, mk = _assert_names()
    picked = []

    def walk(body, ok):
        for st in body:
            if isinstance(st, ast.Expr) and isinstance(st.value, ast.Call) and ok:
                c = st.value
                f = c.func
                good = isinstance(f, ast.Attribute) and all(_pure_arg(a) for a in c.args) and all(
                    _pure_arg(k.value) for k in c.keywords)
                if good and f.attr in tc and isinstance(f.value, ast.Name) and f.value.id == "self":
                    good = f.attr not in helper_defs
                elif good and f.attr in mk:
                    good = _pure_arg(f.value)
                else:
                    good = False
                if good and set(range(st.lineno, st.end_lineno + 1)) <= gone:
                    picked.append(st)
                    continue
            if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef)):
                walk(st.body, True)
            elif isinstance(st, ast.ClassDef):
                walk(st.body, False)
            elif isinstance(st, (ast.If, ast.For, ast.While)):
                walk(st.body, ok)
                walk(st.orelse, ok)
            else:
                for blk in ("body", "orelse", "finalbody", "handlers", "cases"):
                    for x in getattr(st, blk, None) or ():
                        walk(getattr(x, "body", None) or [x] if not isinstance(x, ast.stmt) else [x], False)
    walk(to.body, False)
    covered = set()
    for st in picked:
        covered |= set(range(st.lineno, st.end_lineno + 1))
    if any(ln not in covered and ol[ln - 1].strip() and not ol[ln - 1].strip().startswith("#") for ln in gone):
        return 0
    ids = {id(st) for st in picked}

    class Drop(ast.NodeTransformer):
        def generic_visit(self, node):
            super().generic_visit(node)
            for blk in ("body", "orelse", "finalbody"):
                v = getattr(node, blk, None)
                if isinstance(v, list):
                    setattr(node, blk, [x for x in v if id(x) not in ids])
            return node
    if ast.dump(Drop().visit(to)) != ast.dump(tn):
        return 0
    return len(picked)


def _enclosing_def(node, parent):
    p = parent.get(id(node))
    while p is not None and not isinstance(p, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        p = parent.get(id(p))
    return p


def _mod_file(mod):

    for rel in (mod.replace(".", "/") + ".py", mod.replace(".", "/") + "/__init__.py"):
        if (SRC / rel).exists():
            return rel
    return None


def log(*a):
    print(*a, file=sys.stderr)




HUNK = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


def _raw_clean_paths(raw):


    out = set()
    for sec in re.split(rb"(?m)^(?=diff --git )", raw):
        if b"\r" in sec:
            continue
        try:
            t = sec.decode("utf-8")
        except UnicodeDecodeError:
            continue
        m = re.match(r"diff --git a/(.*) b/(.*)$", t.split("\n", 1)[0])
        if m:
            out |= {m.group(1), m.group(2)}
    return out


def parse_patch(text):

    files, cur = [], None
    lines = text.split("\n")
    i = 0
    while i < len(lines):
        ln = lines[i]
        if ln.startswith("diff --git "):
            cur = {"old": None, "new": None, "hunks": [], "binary": False}
            files.append(cur)
            m = re.match(r"diff --git a/(.*) b/(.*)$", ln)
            if m:
                cur["old"], cur["new"] = m.group(1), m.group(2)
        elif ln.startswith("--- ") and i + 1 < len(lines) and lines[i + 1].startswith("+++ "):
            if cur is None or cur["hunks"]:
                cur = {"old": None, "new": None, "hunks": [], "binary": False}
                files.append(cur)
            a, b = ln[4:].split("\t")[0], lines[i + 1][4:].split("\t")[0]
            cur["old"] = None if a == "/dev/null" else re.sub(r"^a/", "", a)
            cur["new"] = None if b == "/dev/null" else re.sub(r"^b/", "", b)
            i += 1
        elif ln.startswith("Binary files") or ln.startswith("GIT binary patch"):
            if cur is not None:
                cur["binary"] = True
        elif ln.startswith("rename from ") and cur is not None:
            cur["old"] = ln[len("rename from "):]
        elif ln.startswith("rename to ") and cur is not None:
            cur["new"] = ln[len("rename to "):]
        elif ln.startswith("new file mode") and cur is not None:
            cur["created"] = True
        elif ln.startswith("deleted file mode") and cur is not None:
            cur["deleted"] = True
        else:
            m = HUNK.match(ln)
            if m and cur is not None:
                os_, ol, ns, nl = int(m[1]), int(m[2] or 1), int(m[3]), int(m[4] or 1)
                body = []
                left_old, left_new = (ol if m[2] is not None else 1), (nl if m[4] is not None else 1)
                i += 1
                while i < len(lines):
                    l2 = lines[i]
                    if left_old <= 0 and left_new <= 0 and not l2.startswith("\\"):
                        break
                    if l2.startswith((" ", "+", "-")) or l2 == "":
                        t = l2[:1] or " "
                        left_old -= t in " -"
                        left_new -= t in " +"
                        if l2 == "" and (i + 1 >= len(lines) or not lines[i + 1].startswith((" ", "+", "-", "\\"))):
                            break
                        body.append(l2 if l2 else " ")
                    elif l2.startswith("\\"):
                        body.append(l2)
                    else:
                        break
                    i += 1
                cur["hunks"].append((os_, ol, ns, nl, body))
                continue
        i += 1
    for f in files:
        if f.get("created"):
            f["old"] = None
        if f.get("deleted"):
            f["new"] = None
    return files


def apply_hunks(old_text, hunks):

    old = old_text.split("\n")
    out, pos = [], 0
    changed, inserts = set(), set()
    for os_, ol, ns, nl, body in hunks:
        start = os_ - 1 if ol > 0 else os_
        if start < pos:
            raise ValueError("overlapping hunks")
        out.extend(old[pos:start])
        pos = start
        no_newline = False
        for b in body:
            tag, s = b[:1], b[1:]
            if tag == "\\":
                no_newline = True
                continue
            if tag == " ":
                if pos >= len(old) or old[pos] != s:
                    raise ValueError(f"context mismatch at old line {pos + 1}")
                out.append(s)
                pos += 1
            elif tag == "-":
                if pos >= len(old) or old[pos] != s:
                    raise ValueError(f"removed line mismatch at old line {pos + 1}")
                changed.add(pos + 1)
                pos += 1
            elif tag == "+":
                out.append(s)
                inserts.add(pos + 1)
        _ = no_newline
    out.extend(old[pos:])
    return "\n".join(out), changed, inserts




def _canon(c):


    if isinstance(c, types.CodeType):
        return ("<code>", c.co_name)
    if isinstance(c, frozenset):
        return ("frozenset", tuple(sorted((_canon(e) for e in c), key=repr)))
    if isinstance(c, tuple):
        return ("tuple", tuple(_canon(e) for e in c))
    return (type(c).__name__, repr(c))


def _line_number_consts(co):



    if "__firstlineno__" not in co.co_names:
        return ()


    key = (co.co_code, co.co_names)
    cand = _LNC_CACHE.get(key)
    if cand is None:
        import dis
        ins = list(dis.get_instructions(co))
        cand = []
        for a, b in zip(ins, ins[1:]):
            if a.opname == "LOAD_CONST" and b.opname == "STORE_NAME" and b.argval == "__firstlineno__":
                uses = sum(1 for i in ins if i.opname == "LOAD_CONST" and i.arg == a.arg)
                if uses == 1:
                    cand.append(a.arg)
        if len(_LNC_CACHE) > 4096:
            _LNC_CACHE.clear()
        _LNC_CACHE[key] = cand
    return tuple(i for i in cand if type(co.co_consts[i]) is int)


_LNC_CACHE = {}


def _signatures_differ(oco, nco):

    if (oco.co_code != nco.co_code or oco.co_names != nco.co_names or oco.co_varnames != nco.co_varnames
            or oco.co_freevars != nco.co_freevars or oco.co_cellvars != nco.co_cellvars
            or oco.co_argcount != nco.co_argcount or oco.co_posonlyargcount != nco.co_posonlyargcount
            or oco.co_kwonlyargcount != nco.co_kwonlyargcount or oco.co_flags != nco.co_flags
            or getattr(oco, "co_exceptiontable", b"") != getattr(nco, "co_exceptiontable", b"")
            or oco.co_name != nco.co_name or len(oco.co_consts) != len(nco.co_consts)):
        return True
    return _own_signature(oco) != _own_signature(nco)


def _own_signature(co):
    skip = _line_number_consts(co)
    consts = tuple(("<line>",) if i in skip else _canon(c) for i, c in enumerate(co.co_consts))
    return (co.co_code, consts, co.co_names, co.co_varnames, co.co_freevars, co.co_cellvars,
            co.co_argcount, co.co_posonlyargcount, co.co_kwonlyargcount, co.co_flags,
            getattr(co, "co_exceptiontable", b""), co.co_name)


def _walk(co, prefix, out):

    out[prefix] = co
    counts = {}
    for c in co.co_consts:
        if isinstance(c, types.CodeType):
            n = counts.get(c.co_name, 0)
            counts[c.co_name] = n + 1
            _walk(c, f"{prefix}/{c.co_name}#{n}", out)
    return out


def _span(co):
    lines = [ln for _, _, ln in co.co_lines() if ln is not None]
    for c in co.co_consts:
        if isinstance(c, types.CodeType):
            lo, hi = _span(c)
            if lo is not None:
                lines += [lo, hi]
    if co.co_firstlineno:
        lines.append(co.co_firstlineno)
    return (min(lines), max(lines)) if lines else (None, None)












_SIMPLE_HEADER = (ast.If, ast.For, ast.AsyncFor, ast.While, ast.With, ast.AsyncWith)
_DEFS = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
_GAPPY = (ast.Try, ast.Match) + ((ast.TryStar,) if hasattr(ast, "TryStar") else ())


def _first_line(node):
    return min([node.lineno] + [d.lineno for d in getattr(node, "decorator_list", ())])


def _own_range(node):

    if isinstance(node, _SIMPLE_HEADER + _DEFS):
        return _first_line(node), max(_first_line(node), node.body[0].lineno - 1)
    return _first_line(node), node.end_lineno


def _header_range(node):

    if isinstance(node, _GAPPY):
        return None
    return _own_range(node)


class _FileInfo:
    def __init__(self, text):
        self.lines = text.split("\n")
        self.tree = _parse(text)
        self.funcs = {}
        self.strings = set()




        AST, FN, STR = ast.AST, (ast.FunctionDef, ast.AsyncFunctionDef), (ast.Constant, ast.JoinedStr)
        todo = [self.tree]
        pop, push = todo.pop, todo.append
        while todo:
            n = pop()
            if isinstance(n, FN):
                self.funcs.setdefault(_first_line(n), []).append(n)
                if n.lineno != _first_line(n):
                    self.funcs.setdefault(n.lineno, []).append(n)
            elif isinstance(n, STR) and n.end_lineno > n.lineno:
                self.strings.update(range(n.lineno, n.end_lineno + 1))
            lo = getattr(n, "lineno", None)
            if lo is not None and lo == getattr(n, "end_lineno", None):
                continue
            for f in n._fields:
                v = getattr(n, f, None)
                if isinstance(v, AST):
                    push(v)
                elif isinstance(v, list):
                    for x in v:
                        if isinstance(x, AST):
                            push(x)

    def func(self, co):
        c = [n for n in self.funcs.get(co.co_firstlineno, ()) if n.name == co.co_name]
        return c[0] if len(c) == 1 else None

    def ignorable(self, ln):
        t = self.lines[ln - 1].strip() if 0 < ln <= len(self.lines) else ""
        return (t == "" or t.startswith("#")) and ln not in self.strings


def _stmts(fn):


    out = []

    def block(stmts, parent):
        for i, s in enumerate(stmts):
            out.append((s, parent, stmts, i))
            if isinstance(s, _DEFS):
                continue
            for f in ("body", "orelse", "finalbody"):
                b = getattr(s, f, None)
                if isinstance(b, list) and b and isinstance(b[0], ast.stmt):
                    block(b, s)
            for h in getattr(s, "handlers", ()) or ():
                block(h.body, h)
            for c in getattr(s, "cases", ()) or ():
                block(c.body, c)
    block(fn.body, fn)
    return out


def _innermost(stmts, ln):

    best = None
    for e in stmts:
        s = e[0]
        if _first_line(s) <= ln <= s.end_lineno:
            if best is None or (_first_line(s), -s.end_lineno) > (_first_line(best[0]), -best[0].end_lineno):
                best = e
    return best


def _in_nested_body(s, ln):
    return isinstance(s, _DEFS) and ln > _own_range(s)[1]


def _line_diff(hunks, n_old):

    removed, inserted, new2old = set(), set(), {}
    o, n = 1, 1
    for os_, ol, ns, nl, body in hunks:
        start = os_ if ol > 0 else os_ + 1
        while o < start:
            new2old[n] = o
            o += 1
            n += 1
        for b in body:
            t = b[:1]
            if t == " ":
                new2old[n] = o
                o += 1
                n += 1
            elif t == "-":
                removed.add(o)
                o += 1
            elif t == "+":
                inserted.add(n)
                n += 1
    while o <= n_old:
        new2old[n] = o
        o += 1
        n += 1
    return removed, inserted, new2old


def _same_frame(oco, nco):




    return (oco.co_names == nco.co_names and oco.co_varnames == nco.co_varnames and oco.co_cellvars == nco.co_cellvars
            and oco.co_freevars == nco.co_freevars
            and oco.co_flags == nco.co_flags and oco.co_argcount == nco.co_argcount
            and oco.co_posonlyargcount == nco.co_posonlyargcount
            and oco.co_kwonlyargcount == nco.co_kwonlyargcount)


_CLS_LIKE = ("cls", "mcs", "klass", "metacls")


_MUTATORS = {"append", "extend", "pop", "setdefault", "update", "insert", "remove", "clear", "add", "discard",
             "popitem", "appendleft", "extendleft", "sort", "reverse", "__setitem__", "__delitem__", "__iadd__",
             "__ior__"}
_SETATTR = {"setattr", "delattr", "__setattr__", "__delattr__"}


def _walk_stmts(tree):



    todo = [tree]
    while todo:
        n = todo.pop()
        if isinstance(n, ast.stmt):
            yield n
        for f in ("body", "orelse", "finalbody", "handlers", "cases"):
            v = getattr(n, f, None)
            if isinstance(v, list):
                todo.extend(x for x in v if isinstance(x, (ast.stmt, ast.excepthandler, ast.match_case)))


def _class_attrs(fi):

    out = getattr(fi, "_class_attrs", None)
    if out is None:
        out = set()
        for c in _walk_stmts(fi.tree):
            if not isinstance(c, ast.ClassDef):
                continue
            for st in c.body:
                tg = st.targets if isinstance(st, ast.Assign) else [st.target] if isinstance(
                    st, (ast.AugAssign, ast.AnnAssign)) else ()
                stack = list(tg)
                while stack:
                    t = stack.pop()
                    if isinstance(t, (ast.Tuple, ast.List)):
                        stack.extend(t.elts)
                    elif isinstance(t, ast.Starred):
                        stack.append(t.value)
                    elif isinstance(t, ast.Name):
                        out.add(t.id)
        fi._class_attrs = out
    return out


def _writes_persistent(fn, co, fi=None):






    local = set(co.co_varnames) | set(co.co_cellvars) | set(co.co_freevars)
    params = fn.args.posonlyargs + fn.args.args
    first = params[0].arg if params else None
    cls_arg = first if first in _CLS_LIKE else None
    cattrs = _class_attrs(fi) if fi is not None else None

    def shared(obj):

        near = None
        b = obj
        while isinstance(b, (ast.Subscript, ast.Attribute)):
            if isinstance(b, ast.Attribute):
                if b.attr == "__class__":
                    return True
                near = b.attr
            b = b.value
        if isinstance(b, ast.Call):
            return True
        if isinstance(b, ast.Name):
            if b.id == cls_arg or b.id not in local:
                return True
            if b.id == first and near is not None and (cattrs is None or near in cattrs):
                return True
        return False

    todo = list(fn.body)
    while todo:
        n = todo.pop()
        if isinstance(n, (ast.Global, ast.Nonlocal)):
            return True
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)):
            continue
        if isinstance(n, ast.Call):
            f = n.func
            if (isinstance(f, ast.Name) and f.id in _SETATTR) or (isinstance(f, ast.Attribute) and f.attr in _SETATTR):
                return True
            if isinstance(f, ast.Attribute) and f.attr in _MUTATORS and shared(f.value):
                return True
        tgts = ()
        if isinstance(n, ast.Assign):
            tgts = n.targets
        elif isinstance(n, (ast.AugAssign, ast.AnnAssign)):
            tgts = [n.target]
        elif isinstance(n, ast.Delete):
            tgts = n.targets
        elif isinstance(n, (ast.For, ast.AsyncFor, ast.comprehension)):
            tgts = [n.target]
        elif isinstance(n, (ast.withitem,)) and n.optional_vars is not None:
            tgts = [n.optional_vars]
        stack = list(tgts)
        while stack:
            t = stack.pop()
            if isinstance(t, (ast.Tuple, ast.List)):
                stack.extend(t.elts)
            elif isinstance(t, ast.Starred):
                stack.append(t.value)
            elif isinstance(t, (ast.Subscript, ast.Attribute)) and shared(t.value):
                return True
        todo.extend(ast.iter_child_nodes(n))
    return False


def _code_lines(co):
    return {ln for _, _, ln in co.co_lines() if ln is not None}














_NO_FALLTHROUGH = {"RETURN_VALUE", "RETURN_CONST", "RAISE_VARARGS", "RERAISE", "JUMP_FORWARD", "JUMP_BACKWARD",
                   "JUMP_BACKWARD_NO_INTERRUPT", "JUMP"}
_SKIP_OPS = {"NOP", "EXTENDED_ARG", "CACHE"}

_FRAME_NAMES = {"locals", "vars", "exec", "eval", "_getframe", "currentframe", "f_locals", "f_back", "dir", "globals"}


def _relaxable_frame(oco, nco):


    if not (oco.co_flags == nco.co_flags and oco.co_argcount == nco.co_argcount
            and oco.co_posonlyargcount == nco.co_posonlyargcount and oco.co_kwonlyargcount == nco.co_kwonlyargcount
            and oco.co_cellvars == nco.co_cellvars and oco.co_freevars == nco.co_freevars):
        return False
    n = oco.co_argcount + oco.co_kwonlyargcount + bool(oco.co_flags & 0x04) + bool(oco.co_flags & 0x08)
    if oco.co_varnames[:n] != nco.co_varnames[:n]:
        return False
    return not (_FRAME_NAMES & (set(oco.co_names) | set(nco.co_names)))


def _instructions(co, line_key):



    import dis
    every = list(dis.get_instructions(co))
    ins = [i for i in every if i.opname not in _SKIP_OPS]
    ident, count = {}, {}
    for i in ins:
        k = line_key(i.positions.lineno if i.positions else None)
        n = count.get(k, 0)
        count[k] = n + 1
        ident[i.offset] = (k, n)
    resolved, nxt = {}, ("<end>",)
    for i in reversed(every):
        if i.offset in ident:
            nxt = ident[i.offset]
        resolved[i.offset] = nxt

    def where(off):
        return resolved.get(off, ("<off>",))

    if not hasattr(dis, "_parse_exception_table"):
        raise ValueError("exception table not readable")
    table = dis._parse_exception_table(co)
    hasjump = set(getattr(dis, "hasjump", ())) | set(dis.hasjrel) | set(dis.hasjabs)
    hasconst, names = set(dis.hasconst), set(dis.hasname) | set(dis.haslocal) | set(dis.hasfree)
    elems, preds = {}, {}
    for idx, i in enumerate(ins):
        me, outs, tgt = ident[i.offset], [], None
        if i.opcode in hasjump:
            t = getattr(i, "jump_target", None)
            tgt = where(i.argval if t is None else t)
            arg = "->"
            outs.append(tgt)
        elif i.opcode in hasconst:
            arg = _canon(i.argval)
        elif i.opcode in names:
            arg = i.argrepr
        else:
            arg = (i.arg, i.argrepr)
        h = None
        for e in table:
            if e.start <= i.offset < e.end:
                h = (where(e.target), e.depth, e.lasti)
                outs.append(h[0])
                break
        if i.opname in _NO_FALLTHROUGH:
            succ = None
        else:
            succ = ident[ins[idx + 1].offset] if idx + 1 < len(ins) else ("<end>",)
            outs.append(succ)
        elems[me] = (i.opname, arg, tgt, h, succ)
        for o in outs:
            preds.setdefault(o, set()).add(me)
    return elems, preds


def _divergent_lines(oco, nco, new2old):





    old, opred = _instructions(oco, lambda ln: ln)
    new, _ = _instructions(nco, lambda ln: ln if ln is None else new2old.get(ln, ("new", ln)))
    out, todo, seen = set(), [], set()
    for k, v in old.items():
        w = new.get(k)
        if w == v:
            continue
        if w is None or w[:2] != v[:2] or (v[3] is None) != (w[3] is None) or (v[3] and v[3][1:] != w[3][1:]):
            todo.append(k)
            continue


        for a, b in ((v[2], w[2]), (v[3] and v[3][0], w[3] and w[3][0]), (v[4], w[4])):
            if a != b:
                todo.append(a if a is not None and isinstance(a[0], int) else k)
    while todo:
        k = todo.pop()
        if k in seen:
            continue
        seen.add(k)
        if k[0] is None:
            if not opred.get(k):
                return None
            todo.extend(opred[k])
        elif isinstance(k[0], int):
            out.add(k[0])
    return out


def statement_ranges(oco, nco, old_fi, new_fi, diff):


    same = _same_frame(oco, nco)
    if not same and not (FRAME_DIFF and _relaxable_frame(oco, nco)):
        return None
    ofn, nfn = old_fi.func(oco), new_fi.func(nco)
    if ofn is None or nfn is None:
        return None
    if _writes_persistent(ofn, oco, old_fi) or _writes_persistent(nfn, nco, new_fi):
        return None
    removed, inserted, new2old = diff
    ost, nst = _stmts(ofn), _stmts(nfn)
    by_first = {}
    for e in ost:
        by_first.setdefault(_first_line(e[0]), e[0])
    olines = _code_lines(oco)
    targets = []

    def doc(fn, s):
        b = fn.body[0]
        return (s is b and isinstance(b, ast.Expr) and isinstance(b.value, ast.Constant)
                and isinstance(b.value.value, str))

    def target_old(s):
        r = _own_range(s)
        if not any(r[0] <= ln <= r[1] for ln in olines):
            return False
        targets.append(r)
        return True

    def old_twin(node):
        o = new2old.get(_first_line(node))
        t = by_first.get(o) if o is not None else None
        return t if t is not None and type(t) is type(node) else None

    def position(entry, depth=0):

        s, parent, blk, i = entry
        if depth > 200:
            return False



        oparent = ofn if parent is nfn else old_twin(parent) if isinstance(parent, _SIMPLE_HEADER) else None
        if oparent is not None:
            field = next((f for f in ("body", "orelse") if getattr(parent, f, None) is blk), None)
            oblk = getattr(oparent, field, None) if field else None
            if oblk and len(oblk) == len(blk) and target_old(oblk[i]):
                return True
        if i > 0:
            prev = blk[i - 1]
            t = old_twin(prev)
            if t is not None:
                return target_old(t)
            return position(next(x for x in nst if x[0] is prev), depth + 1)
        if parent is nfn or not isinstance(parent, _SIMPLE_HEADER):
            return False
        t = old_twin(parent)
        if t is not None:
            return target_old(t)
        return position(next(x for x in nst if x[0] is parent), depth + 1)

    for ln in sorted(removed):
        if not _first_line(ofn) <= ln <= ofn.end_lineno or old_fi.ignorable(ln):
            continue
        e = _innermost(ost, ln)
        if e is None or doc(ofn, e[0]):
            return None
        s = e[0]
        if _in_nested_body(s, ln):
            continue
        h = _header_range(s)
        if h is None or not h[0] <= ln <= h[1] or not target_old(s):
            return None
    for ln in sorted(inserted):
        if not _first_line(nfn) <= ln <= nfn.end_lineno or new_fi.ignorable(ln):
            continue
        e = _innermost(nst, ln)
        if e is None or doc(nfn, e[0]):
            return None
        s = e[0]
        if _in_nested_body(s, ln):
            continue
        h = _header_range(s)
        if h is None or not h[0] <= ln <= h[1]:
            return None
        t = old_twin(s)
        if not (target_old(t) if t is not None else position(e)):
            return None
    if FRAME_DIFF:

        div = _divergent_lines(oco, nco, new2old)
        if div is None:
            return None
        for ln in sorted(div):
            e = _innermost(ost, ln)
            if e is None or doc(ofn, e[0]):
                return None
            s = e[0]
            if _in_nested_body(s, ln):
                return None
            h = _header_range(s)
            if h is None or not h[0] <= ln <= h[1] or not target_old(s):
                return None
    return targets or None


_compiled = {}


def _src_bytes(text):



    return text.encode("utf-8", "surrogatepass")


CACHE = APP / "cache"


def _cache_file(kind, path):
    return CACHE / kind / (path.replace("/", "__") + ".bin")


def compile_old(path, text):
    co = _compiled.get(path)
    if co is None:
        co = _load_old_code(path, text)
        if co is None:
            co = compile(_src_bytes(text), path, "exec", dont_inherit=True)
        _compiled[path] = co
    return co


def _load_old_code(path, text):


    import hashlib
    import marshal
    try:
        raw = _cache_file("code", path).read_bytes()
    except OSError:
        return None
    if raw[:40] != hashlib.sha1(text.encode("utf-8", "surrogatepass")).hexdigest().encode():
        return None
    try:
        co = marshal.loads(raw[40:])
    except Exception:
        return None
    return co if isinstance(co, types.CodeType) and co.co_filename == path else None


def code_changes(path, old_text, new_text, hunks=None):




    try:
        new_co = compile(_src_bytes(new_text), path, "exec", dont_inherit=True)
    except (SyntaxError, ValueError):
        return "syntax", []
    old_co = compile_old(path, old_text)
    old_map, new_map = _walk(old_co, "", {}), _walk(new_co, "", {})
    regions = []
    info = {}

    def narrowed(oco, nco):
        if hunks is None:
            return None
        try:
            if not info:
                info["o"], info["n"] = _FileInfo(old_text), _FileInfo(new_text)
                info["d"] = _line_diff(hunks, len(old_text.split("\n")))
            return statement_ranges(oco, nco, info["o"], info["n"], info["d"])
        except Exception:
            return None

    def add(co, ranges=None):


        own = (_code_lines(co) - {co.co_firstlineno}) or _code_lines(co)
        regions.append((kind(co), ranges or [_span(co)], co.co_qualname, _span(co), own))

    def scope_of(key):

        return key.rsplit("/", 1)[0] if "/" in key else ""

    def kind(co):
        return "func" if co.co_flags & 0x0002 else "scope"

    for key, oco in old_map.items():
        nco = new_map.get(key)
        if nco is None:
            add(oco)
            parent = old_map.get(scope_of(key))
            if parent is not None and key:
                add(parent)
        elif _signatures_differ(oco, nco):
            add(oco, narrowed(oco, nco) if kind(oco) == "func" else None)
    for key in new_map:
        if key not in old_map:

            k = scope_of(key)
            while k not in old_map and k:
                k = scope_of(k)
            parent = old_map.get(k, old_co)
            add(parent)
    if not regions:
        return "null", []
    return "changed", regions




_DEF = (ast.FunctionDef, ast.AsyncFunctionDef)
_COMPOUND = (ast.If, ast.Try, ast.With, ast.AsyncWith, ast.For, ast.AsyncFor) + (
    (ast.TryStar,) if hasattr(ast, "TryStar") else ())


def _bound(t, out):
    if isinstance(t, ast.Name):
        out.add(t.id)
        return True
    if isinstance(t, (ast.Tuple, ast.List)):
        return all([_bound(e, out) for e in t.elts])
    if isinstance(t, ast.Starred):
        return _bound(t.value, out)
    return False


def _sig(node):


    if isinstance(node, _DEF):
        body, node.body = node.body, []
        try:
            return ast.dump(node)
        finally:
            node.body = body
    return ast.dump(node)


def _top_level(tree):


    names, effects = {}, []

    def visit(stmts):
        for n in stmts:
            bound, pure = set(), True
            if isinstance(n, (ast.Import, ast.ImportFrom)):
                for a in n.names:
                    bound.add((a.asname or a.name).split(".")[0])
                    if a.name == "*":
                        pure = False
            elif isinstance(n, ast.ClassDef):
                continue
            elif isinstance(n, _DEF):
                bound.add(n.name)
            elif isinstance(n, ast.Assign):
                pure = all([_bound(t, bound) for t in n.targets])
            elif isinstance(n, (ast.AnnAssign, ast.AugAssign)):
                pure = _bound(n.target, bound)
            elif isinstance(n, ast.Expr) and isinstance(n.value, ast.Constant):
                continue
            elif isinstance(n, ast.Pass):
                continue
            elif isinstance(n, _COMPOUND):
                saved = {f: getattr(n, f) for f in ("body", "orelse", "finalbody", "handlers") if hasattr(n, f)}
                for f in saved:
                    setattr(n, f, [])
                try:
                    head = ast.dump(n)
                finally:
                    for f, v in saved.items():
                        setattr(n, f, v)
                inner_names, inner_effects = _top_level(ast.Module(
                    body=[x for f in ("body", "orelse", "finalbody") for x in saved.get(f, [])]
                    + [x for h in saved.get("handlers", []) for x in h.body], type_ignores=[]))
                for k, v in inner_names.items():
                    names.setdefault(k, []).extend([head] + v)
                effects.extend([head + e for e in inner_effects])
                if isinstance(n, (ast.For, ast.AsyncFor)) and not _bound(n.target, set()):
                    effects.append(head)
                continue
            else:
                pure = False
            sig = _sig(n)
            for b in bound:
                names.setdefault(b, []).append(sig)
            if not pure:
                effects.append(sig)
    visit(tree.body)
    return names, effects


def top_level_changes(old_text, new_text):

    on, oe = _top_level(_parse(old_text))
    nn, ne = _top_level(_parse(new_text))
    changed = {k for k, v in on.items() if sorted(v) != sorted(nn.get(k, []))}
    added = set(nn) - set(on)
    return changed, added, sorted(oe) != sorted(ne)


_NR_INDEX = {}


def name_reads(text, names):




    ix = _NR_INDEX.get(text)
    if ix is None:
        ix = _NR_INDEX[text] = _nr_prebuilt(text) or _name_reads_index(text)
    aliases, loads = ix
    want = set(names)
    for n in names:
        want.update(aliases.get(n, ()))
    out = []
    for ident in want:
        for lo, hi, in_func in loads.get(ident, ()):
            if not in_func:
                return None
            out.append((lo, hi))
    return out


_NR_BUILT = None


def _nr_prebuilt(text):

    global _NR_BUILT
    import hashlib
    if _NR_BUILT is None:
        try:
            import pickle
            with open(CACHE / "name_reads.pickle", "rb") as fh:
                _NR_BUILT = pickle.load(fh)
        except Exception:
            _NR_BUILT = {}
    return _NR_BUILT.get(hashlib.sha1(text.encode("utf-8", "surrogatepass")).hexdigest())


def _name_reads_index(text):

    tree = _parse(text)
    aliases, loads = {}, {}
    for n in ast.walk(tree):
        if isinstance(n, ast.ImportFrom):
            for al in n.names:
                if al.asname:
                    aliases.setdefault(al.name, []).append(al.asname)

    def walk(node, in_func):
        for c in ast.iter_child_nodes(node):
            if isinstance(c, (ast.Import, ast.ImportFrom)):
                continue
            if isinstance(c, (ast.Name, ast.Attribute)) and isinstance(c.ctx, ast.Load):
                loads.setdefault(c.id if isinstance(c, ast.Name) else c.attr, []).append(
                    (c.lineno, c.end_lineno, in_func))
            if isinstance(c, _DEF + (ast.Lambda,)):
                for d in (getattr(c, "decorator_list", []) + c.args.defaults
                          + [k for k in c.args.kw_defaults if k is not None]):
                    walk(ast.Expression(body=d), in_func)
                body = c.body if isinstance(c.body, list) else [c.body]
                walk(ast.Module(body=body, type_ignores=[]) if isinstance(c.body, list)
                     else ast.Expression(body=c.body), True)
                continue
            walk(c, in_func)
    walk(tree, False)
    return aliases, loads


def _name_reads_walk(text, names):

    tree = _parse(text)
    want = set(names)
    for n in ast.walk(tree):
        if isinstance(n, ast.ImportFrom):
            for al in n.names:
                if al.name in names and al.asname:
                    want.add(al.asname)
    out = []

    def walk(node, in_func):
        for c in ast.iter_child_nodes(node):
            if isinstance(c, (ast.Import, ast.ImportFrom)):
                continue
            if isinstance(c, (ast.Name, ast.Attribute)) and (c.id if isinstance(c, ast.Name) else c.attr) in want \
                    and isinstance(c.ctx, ast.Load):
                if not in_func:
                    raise LookupError
                out.append((c.lineno, c.end_lineno))
            if isinstance(c, _DEF + (ast.Lambda,)):
                for d in (getattr(c, "decorator_list", []) + c.args.defaults
                          + [k for k in c.args.kw_defaults if k is not None]):
                    walk(ast.Expression(body=d), in_func)
                body = c.body if isinstance(c.body, list) else [c.body]
                walk(ast.Module(body=body, type_ignores=[]) if isinstance(c.body, list)
                     else ast.Expression(body=c.body), True)
                continue
            walk(c, in_func)
    try:
        walk(tree, False)
    except LookupError:
        return None
    return out


def import_scope_names(text):



    tree = _parse(text)
    funcs = {n.name: n for n in tree.body if isinstance(n, _DEF)}
    out = set()

    def loads(root, into, enter):
        todo = list(root.body) if enter else [root]
        while todo:
            n = todo.pop()
            if isinstance(n, _DEF):
                todo.extend(n.decorator_list)
                todo.extend(n.args.defaults)
                todo.extend(d for d in n.args.kw_defaults if d is not None)
                continue
            if isinstance(n, ast.Lambda):
                todo.extend(n.args.defaults)
                continue
            if isinstance(n, ast.Name):
                into.add(n.id)
            elif isinstance(n, ast.Attribute):
                into.add(n.attr)
            todo.extend(ast.iter_child_nodes(n))

    for n in tree.body:
        loads(n, out, False)
    done = set()
    while True:
        more = [f for f in funcs if f in out and f not in done]
        if not more:
            break
        for f in more:
            done.add(f)
            loads(funcs[f], out, True)
    return out








_IMPORT_PROBE = r"""
import unittest  # the test environment (see above)
import importlib.abc, importlib.util, json, sys
_cfg = json.load(open(sys.argv[1], encoding="utf-8"))
patched = _cfg["patched"]  # {module name: [source, is_pkg, origin]}
root = sys.argv[2]
class Finder(importlib.abc.MetaPathFinder, importlib.abc.Loader):
    def find_spec(self, name, path, target=None):
        if name in patched:
            is_pkg = patched[name][1]
            return importlib.util.spec_from_loader(name, self, origin=patched[name][2], is_package=is_pkg)
        return None
    def create_module(self, spec):
        return None
    def exec_module(self, module):
        src, is_pkg, origin = patched[module.__name__]
        if is_pkg:
            module.__path__ = [origin.rsplit("/", 1)[0]]
        module.__file__ = origin
        exec(compile(src.encode("utf-8", "surrogatepass"), origin, "exec"), module.__dict__)
sys.path.insert(0, root)
sys.meta_path.insert(0, Finder())
# Third-party packages the test modules import at top level (duckdb, pandas, pytz, setuptools) are
# not in this image. A test module asking for one that no finder can locate gets a permissive stub,
# so its import runs on to the sqlglot code it exercises (collection probe). Only requests made
# directly by a tests.* module are served, and only after every real finder said no.
class _StubMeta(type):
    def __getattr__(cls, n):
        if n.startswith("__"):
            raise AttributeError(n)
        return cls
    def __call__(cls, *a, **k):
        return cls
    def __iter__(cls):
        return iter(())
class _Stub(metaclass=_StubMeta):
    pass
class _StubFinder(importlib.abc.MetaPathFinder, importlib.abc.Loader):
    def find_spec(self, name, path, target=None):
        f = sys._getframe(1)
        while f is not None and f.f_globals.get("__name__", "").startswith(("importlib", "_frozen_importlib")):
            f = f.f_back
        who = "" if f is None else f.f_globals.get("__name__", "")
        top = name.split(".")[0]
        if top in ("sqlglot", "tests") or not (who.startswith("tests.") or top in _stubbed):
            return None
        _stubbed.add(name.split(".")[0])
        return importlib.util.spec_from_loader(name, self, is_package=True)
    def create_module(self, spec):
        m = type(sys)(spec.name)
        m.__getattr__ = lambda n: (_ for _ in ()).throw(AttributeError(n)) if n.startswith("__") else _Stub
        return m
    def exec_module(self, module):
        module.__path__ = []
_stubbed = set()
sys.meta_path.append(_StubFinder())
failed = []
try:
    import sqlglot
except BaseException as e:
    failed.append("sqlglot")
for name in (_cfg["extra"] if _cfg.get("extra_only") else list(patched) + _cfg["extra"]):
    try:
        importlib.import_module(name)
    except BaseException as e:
        failed.append(name)
print(json.dumps(failed))
"""


_BASELINE = None


def _baseline_failures():


    global _BASELINE
    if _BASELINE is None:
        f = APP / "import_baseline.json"
        if f.exists():
            _BASELINE = set(json.loads(f.read_text(encoding="utf-8")))
        else:
            _BASELINE = set()
            _BASELINE = _probe_all()
    return _BASELINE


def importable(path):



    return path.endswith(".py") and (path.startswith("sqlglot/") or (
        path.startswith("tests/") and not Path(path).name.startswith("test_")))


def _all_modules():
    out = []
    for p in sorted([*(SRC / "sqlglot").rglob("*.py"), *(SRC / "tests").rglob("*.py")]):
        if not importable(p.relative_to(SRC).as_posix()):
            continue
        rel = p.relative_to(SRC).as_posix()
        name = rel[:-3].replace("/", ".")
        out.append(name[: -len(".__init__")] if name.endswith(".__init__") else name)
    return out


def _probe_all():
    import subprocess
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8") as fh:
        json.dump({"patched": {}, "extra": _all_modules()}, fh)
        tmp = fh.name
    try:
        r = subprocess.run([sys.executable, "-I", "-S", "-c", _IMPORT_PROBE, tmp, str(SRC)],
                           capture_output=True, text=True, timeout=300)
        return set(json.loads(r.stdout.strip().splitlines()[-1]))
    finally:
        os.unlink(tmp)











_PROBE_SERVER = r"""
import unittest  # the test environment (see _IMPORT_PROBE)
import importlib.abc, importlib.util, json, sys, os
patched = {}
root = sys.argv[1]
class Finder(importlib.abc.MetaPathFinder, importlib.abc.Loader):
    def find_spec(self, name, path, target=None):
        if name in patched:
            is_pkg = patched[name][1]
            return importlib.util.spec_from_loader(name, self, origin=patched[name][2], is_package=is_pkg)
        return None
    def create_module(self, spec):
        return None
    def exec_module(self, module):
        src, is_pkg, origin = patched[module.__name__]
        if is_pkg:
            module.__path__ = [origin.rsplit("/", 1)[0]]
        module.__file__ = origin
        exec(compile(src.encode("utf-8", "surrogatepass"), origin, "exec"), module.__dict__)
class _Asked(importlib.abc.MetaPathFinder):
    def find_spec(self, name, path, target=None):
        _asked.add(name)
        return None
_asked = set()
sys.argv = ["-c", "", root]
sys.path.insert(0, root)
sys.meta_path.insert(0, Finder())
# Third-party packages the test modules import at top level (duckdb, pandas, pytz, setuptools) are
# not in this image. A test module asking for one that no finder can locate gets a permissive stub,
# so its import runs on to the sqlglot code it exercises (collection probe). Only requests made
# directly by a tests.* module are served, and only after every real finder said no.
class _StubMeta(type):
    def __getattr__(cls, n):
        if n.startswith("__"):
            raise AttributeError(n)
        return cls
    def __call__(cls, *a, **k):
        return cls
    def __iter__(cls):
        return iter(())
class _Stub(metaclass=_StubMeta):
    pass
class _StubFinder(importlib.abc.MetaPathFinder, importlib.abc.Loader):
    def find_spec(self, name, path, target=None):
        f = sys._getframe(1)
        while f is not None and f.f_globals.get("__name__", "").startswith(("importlib", "_frozen_importlib")):
            f = f.f_back
        who = "" if f is None else f.f_globals.get("__name__", "")
        top = name.split(".")[0]
        if top in ("sqlglot", "tests") or not (who.startswith("tests.") or top in _stubbed):
            return None
        _stubbed.add(name.split(".")[0])
        return importlib.util.spec_from_loader(name, self, is_package=True)
    def create_module(self, spec):
        m = type(sys)(spec.name)
        m.__getattr__ = lambda n: (_ for _ in ()).throw(AttributeError(n)) if n.startswith("__") else _Stub
        return m
    def exec_module(self, module):
        module.__path__ = []
_stubbed = set()
sys.meta_path.append(_StubFinder())
_rec = _Asked()
sys.meta_path.insert(0, _rec)
_ok = True
try:
    import sqlglot
except BaseException:
    _ok = False
sys.meta_path.remove(_rec)
sys.stderr.flush()
_asked |= set(sys.modules)
os.write(1, (json.dumps({"ok": _ok, "asked": sorted(_asked)}) + "\n").encode())
_inp = sys.stdin.buffer
import gc
def _gc_child():
    # CPU only: the warm parent's objects are permanent for the fork (no rescans of the loaded
    # package, no copy-on-write faults from the collector); young garbage is still collected
    gc.freeze()
    gc.set_threshold(20000, 50, 1000)
while _ok:
    _line = _inp.readline()
    if not _line:
        break
    _req = json.loads(_line)
    sys.stdout.flush()
    sys.stderr.flush()
    _pid = os.fork()
    if _pid == 0:
        _gc_child()
        _fd = os.open(_req["out"], os.O_WRONLY | os.O_TRUNC)
        os.dup2(_fd, 1)
        os.close(_fd)
        _fd = os.open(_req["err"], os.O_WRONLY | os.O_APPEND)
        os.dup2(_fd, 2)
        os.close(_fd)
        _fd = os.open(os.devnull, os.O_RDONLY)
        os.dup2(_fd, 0)
        os.close(_fd)
        sys.argv = ["-c", _req["cfg"], root]
        _cfg = json.load(open(sys.argv[1], encoding="utf-8"))
        patched.update(_cfg["patched"])
        failed = []
        try:
            import sqlglot
        except BaseException as e:
            failed.append("sqlglot")
        for name in (_cfg["extra"] if _cfg.get("extra_only") else list(patched) + _cfg["extra"]):
            try:
                importlib.import_module(name)
            except BaseException as e:
                failed.append(name)
        print(json.dumps(failed))
        # the verdict is printed: skip interpreter shutdown (module teardown costs CPU and cannot
        # change what was printed)
        sys.stdout.flush()
        sys.stderr.flush()
        os._exit(0)
    os.write(1, (json.dumps({"pid": _pid}) + "\n").encode())
    os.waitpid(_pid, 0)
    os.write(1, b'{"done": 1}\n')
"""


class _ProbeServer:
    def __init__(self):
        self.proc, self.asked, self.dead, self.buf, self.err0 = None, None, False, b"", None

    def _start(self):
        import subprocess
        import tempfile
        fd, self.err0 = tempfile.mkstemp(suffix=".err")
        os.close(fd)
        with open(self.err0, "wb") as err:
            self.proc = subprocess.Popen([sys.executable, "-I", "-S", "-c", _PROBE_SERVER, str(SRC)],
                                         stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=err)
        hello = self._line(PROBE_TIMEOUT_S * 3)
        if not hello or not hello.get("ok"):
            raise RuntimeError("probe server unavailable")
        self.asked = set(hello["asked"])
        with open(self.err0, "rb") as fh:
            self.prefix = fh.read()

    def _line(self, timeout):
        import select
        deadline = time.monotonic() + timeout
        fd = self.proc.stdout.fileno()
        while b"\n" not in self.buf:
            left = deadline - time.monotonic()
            if left <= 0 or not select.select([fd], [], [], left)[0]:
                return None
            chunk = os.read(fd, 65536)
            if not chunk:
                raise RuntimeError("probe server exited")
            self.buf += chunk
        line, self.buf = self.buf.split(b"\n", 1)
        return json.loads(line)

    def asked_names(self):

        if self.dead or not hasattr(os, "fork"):
            return None
        w0 = time.monotonic()
        try:
            if self.proc is None:
                self._start()
            return self.asked
        except Exception as e:
            log(f"probe server off ({type(e).__name__}: {e}): cold probes from here on")
            self.close()
            self.dead = True
            return None

    def run(self, cfg, names):

        import io
        import subprocess
        import tempfile
        if self.dead or not hasattr(os, "fork"):
            return None
        w0 = time.monotonic()
        try:
            if self.proc is None:
                self._start()
            if names & self.asked:
                return None
            fo, out = tempfile.mkstemp(suffix=".out")
            fe, err = tempfile.mkstemp(suffix=".err")
            try:
                os.write(fe, self.prefix)
                os.close(fo)
                os.close(fe)
                t0 = time.monotonic()
                self.proc.stdin.write((json.dumps({"cfg": cfg, "out": out, "err": err}) + "\n").encode())
                self.proc.stdin.flush()
                pid = self._line(PROBE_TIMEOUT_S)
                if pid is None:
                    raise RuntimeError("probe server not answering")
                done = self._line(max(0.0, PROBE_TIMEOUT_S - (time.monotonic() - t0)))
                if done is None:
                    try:
                        os.kill(pid["pid"], 9)
                    except OSError:
                        pass
                    if self._line(PROBE_TIMEOUT_S) is None:
                        raise RuntimeError("probe server stuck")
                    raise subprocess.TimeoutExpired("probe", PROBE_TIMEOUT_S)

                def text(p):
                    with open(p, "rb") as fh:
                        return io.TextIOWrapper(io.BytesIO(fh.read())).read()
                return subprocess.CompletedProcess("probe", 0, text(out), text(err))
            finally:
                for p in (out, err):
                    try:
                        os.unlink(p)
                    except OSError:
                        pass
        except subprocess.TimeoutExpired:
            raise
        except Exception as e:
            log(f"probe server off ({type(e).__name__}: {e}): cold probes from here on")
            self.close()
            self.dead = True
            return None

    def close(self):
        if self.proc is not None:
            try:
                self.proc.stdin.close()
                self.proc.wait(timeout=PROBE_TIMEOUT_S)
            except Exception:
                self.proc.kill()
                self.proc.wait()
            self.proc = None
        if self.err0:
            try:
                os.unlink(self.err0)
            except OSError:
                pass
            self.err0 = None


class _E2Server:



    def __init__(self):
        self.proc, self.dead, self.buf = None, False, b""

    def _line(self, timeout):
        import select
        deadline = time.monotonic() + timeout
        fd = self.proc.stdout.fileno()
        while b"\n" not in self.buf:
            left = deadline - time.monotonic()
            if left <= 0 or not select.select([fd], [], [], left)[0]:
                return None
            chunk = os.read(fd, 65536)
            if not chunk:
                raise RuntimeError("E2 server exited")
            self.buf += chunk
        line, self.buf = self.buf.split(b"\n", 1)
        return json.loads(line)

    def run(self, cfg, timeout):

        import subprocess
        import tempfile
        if self.dead or not hasattr(os, "fork") or os.environ.get("RWX_E2_FORK", "1") != "1":
            return None
        try:
            if self.proc is None:
                self.proc = subprocess.Popen(
                    [sys.executable, "-I", "-S", str(APP / "e2_ns.py"), "serve", str(SRC), str(E2_FP)],
                    stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                    env={**os.environ, "PYTHONHASHSEED": "0"}, cwd=tempfile.gettempdir())
                hello = self._line(timeout)
                if not hello or not hello.get("ok"):
                    raise RuntimeError("E2 server unavailable")
            fo, out = tempfile.mkstemp(suffix=".out")
            os.close(fo)
            try:
                t0 = time.monotonic()
                self.proc.stdin.write((json.dumps({"cfg": cfg, "out": out}) + "\n").encode())
                self.proc.stdin.flush()
                pid = self._line(timeout)
                if pid is None:
                    raise RuntimeError("E2 server not answering")
                done = self._line(max(0.0, timeout - (time.monotonic() - t0)))
                if done is None:
                    try:
                        os.kill(pid["pid"], 9)
                    except OSError:
                        pass
                    if self._line(timeout) is None:
                        raise RuntimeError("E2 server stuck")
                    raise subprocess.TimeoutExpired("e2", timeout)
                with open(out, "rb") as fh:
                    import io
                    return io.TextIOWrapper(io.BytesIO(fh.read())).read()
            finally:
                os.unlink(out)
        except subprocess.TimeoutExpired:
            raise
        except Exception as e:
            log(f"E2 server off ({type(e).__name__}: {e}): cold diffs from here on")
            self.close()
            self.dead = True
            return None

    def close(self):
        if self.proc is not None:
            try:
                self.proc.stdin.close()
                self.proc.wait(timeout=PROBE_TIMEOUT_S)
            except Exception:
                self.proc.kill()
                self.proc.wait()
            self.proc = None


_E2_SERVER = _E2Server()
_SERVER = None


def _probe_server():
    global _SERVER
    if _SERVER is None:
        _SERVER = _ProbeServer()
    return _SERVER


def _close_probe_server():
    if _SERVER is not None:
        _SERVER.close()
    _E2_SERVER.close()
    e1 = sys.modules.get("e1_cutoff")
    if e1 is not None and hasattr(e1, "close_server"):
        e1.close_server()


def import_fails(src_root, patched_files, also_import=(), baseline=None, in_order=False):


    import subprocess
    import tempfile
    mods = {}
    for rel, text in patched_files.items():
        name = rel[:-3].replace("/", ".")
        is_pkg = name.endswith(".__init__")
        if is_pkg:
            name = name[: -len(".__init__")]
        mods[name] = [text, is_pkg, str(Path(src_root) / rel).replace("\\", "/")]
    extra = []
    for rel in also_import:
        name = rel[:-3].replace("/", ".")
        extra.append(name[: -len(".__init__")] if name.endswith(".__init__") else name)
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8") as fh:


        json.dump({"patched": mods, "extra": extra, "extra_only": in_order}, fh)
        tmp = fh.name
    try:
        r = None
        if str(src_root) == str(SRC):
            r = _probe_server().run(tmp, set(mods))
        if r is None:
            r = subprocess.run([sys.executable, "-I", "-S", "-c", _IMPORT_PROBE, tmp, str(src_root)],
                               capture_output=True, text=True, timeout=PROBE_TIMEOUT_S)
        try:
            failed = set(json.loads(r.stdout.strip().splitlines()[-1]))
        except Exception:
            return True, "probe crashed: " + r.stderr[-200:]

        new_fail = sorted(failed - (_baseline_failures() if baseline is None else baseline))
        return bool(new_fail), ", ".join(new_fail)
    except subprocess.TimeoutExpired:
        return True, "timeout"
    finally:
        os.unlink(tmp)


def test_modules():

    out = []

    def walk(d):
        for p in sorted(d.iterdir(), key=lambda e: e.name):
            if p.is_dir() and (p / "__init__.py").exists():
                walk(p)
            elif p.is_file() and p.name.startswith("test_") and p.suffix == ".py":
                out.append(p.relative_to(SRC).as_posix())
    if (SRC / "tests").is_dir():
        walk(SRC / "tests")
    return out


def _full_probe_files():


    mods = [m.replace(".", "/") for m in _all_modules()]
    return test_modules() + [m + ".py" if (SRC / (m + ".py")).exists() else m + "/__init__.py" for m in mods]


_BASELINE_FULL = None


def _baseline_full():

    global _BASELINE_FULL
    if _BASELINE_FULL is None:
        f = APP / "import_baseline_full.json"
        if f.exists():
            _BASELINE_FULL = set(json.loads(f.read_text(encoding="utf-8")))
        else:
            ok, detail = import_fails(SRC, {}, _full_probe_files(), baseline=set(), in_order=True)
            _BASELINE_FULL = set(detail.split(", ")) if ok and detail else set()
            if ok and (detail == "timeout" or detail.startswith("probe crashed")):
                _BASELINE_FULL = None
                raise RuntimeError("baseline probe gave no verdict")
    return _BASELINE_FULL


def _mod_name(rel):
    name = rel[:-3].replace("/", ".")
    return name[: -len(".__init__")] if name.endswith(".__init__") else name


def _func_import_index(root=None):




    root = Path(root or SRC)
    files = {}
    for base in ("sqlglot", "tests"):
        for p in (root / base).rglob("*.py"):
            rel = p.relative_to(root).as_posix()
            files[_mod_name(rel)] = rel
    lazy = set()
    for mod, rel in files.items():
        if rel.endswith("__init__.py"):
            try:
                tree = ast.parse((root / rel).read_text(encoding="utf-8"))
            except (SyntaxError, ValueError, OSError):
                lazy.add(mod)
                continue
            if any(isinstance(n, ast.FunctionDef) and n.name == "__getattr__" for n in tree.body):
                lazy.add(mod)
    under = {}
    for mod in files:
        parts = mod.split(".")
        for i in range(1, len(parts)):
            under.setdefault(".".join(parts[:i]), []).append(mod)
    out, pending, lazy_sites, dynamic = {}, [], [], []
    for mod, rel in files.items():
        try:
            tree = ast.parse((root / rel).read_text(encoding="utf-8"))
        except (SyntaxError, ValueError, OSError):
            continue
        pkg = mod if rel.endswith("__init__.py") else mod.rsplit(".", 1)[0]

        def visit(node, in_func):
            for ch in ast.iter_child_nodes(node):
                f = in_func or isinstance(ch, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda))
                if isinstance(ch, ast.Call) and ch.args and not isinstance(ch.args[0], ast.Constant):
                    fn = ch.func
                    fname = fn.attr if isinstance(fn, ast.Attribute) else getattr(fn, "id", "")
                    if fname in ("import_module", "__import__"):
                        a0 = ch.args[0]
                        pre = a0.values[0].value if (isinstance(a0, ast.JoinedStr) and a0.values and isinstance(
                            a0.values[0], ast.Constant) and isinstance(a0.values[0].value, str)) else ""
                        dynamic.append([pre, rel, ch.lineno, ch.end_lineno or ch.lineno])
                if in_func and isinstance(ch, (ast.Import, ast.ImportFrom)):
                    if isinstance(ch, ast.Import):
                        targets = [a.name for a in ch.names]
                    else:
                        b = ch.module or ""
                        if ch.level:
                            up = pkg.split(".")[: len(pkg.split(".")) - (ch.level - 1)]
                            b = ".".join(up + ([b] if b else []))
                        targets = [b] + [f"{b}.{a.name}" for a in ch.names]
                        if b in lazy:
                            for a in ch.names:
                                pending.append((b, a.name, len(targets)))
                            targets.append(None)
                    hit = set()
                    for t in targets:
                        if t is None:
                            lazy_sites.append((rel, ch.lineno, ch.end_lineno or ch.lineno, pending[-len(ch.names):]))
                            continue
                        ps = t.split(".")
                        for i in range(1, len(ps) + 1):
                            m = ".".join(ps[:i])
                            if m in files and files[m] != rel:
                                hit.add(files[m])
                    for h in hit:
                        out.setdefault(h, []).append([rel, ch.lineno, ch.end_lineno or ch.lineno])
                visit(ch, f)
        visit(tree, False)
    if lazy_sites:
        resolved = _resolve_lazy(root, sorted({f"{b}:{n}" for _, _, _, ps in lazy_sites for b, n, _ in ps}))
        for rel, lo, hi, ps in lazy_sites:
            hit = set()
            for b, n, _ in ps:
                m = resolved.get(f"{b}:{n}")
                hit |= {files[m]} if m in files else {files[x] for x in under.get(b, [])}
            for h in hit - {rel}:
                out.setdefault(h, []).append([rel, lo, hi])
            for b in {b for b, _, _ in ps}:

                out.setdefault("lazy:" + files[b], []).append([rel, lo, hi])
    for pre, rel, lo, hi in dynamic:




        if not rel.startswith("tests/"):
            continue
        for mod, f in files.items():
            if f != rel and mod.startswith(pre):
                out.setdefault(f, []).append([rel, lo, hi])
    return out


_RESOLVE = r"""
import unittest, importlib, inspect, json, sys
sys.path.insert(0, sys.argv[1])
out = {}
for key in json.loads(sys.argv[2]):
    pkg, name = key.split(":")
    try:
        v = getattr(importlib.import_module(pkg), name)
        out[key] = v.__name__ if inspect.ismodule(v) else v.__module__
    except BaseException:
        pass
print(json.dumps(out))
"""


def _resolve_lazy(root, keys):

    import subprocess
    try:
        r = subprocess.run([sys.executable, "-I", "-S", "-c", _RESOLVE, str(root), json.dumps(keys)],
                           capture_output=True, text=True, timeout=120)
        return json.loads(r.stdout.strip().splitlines()[-1])
    except Exception:
        return {}




def _map_digest(raw):
    import hashlib
    return hashlib.sha1(raw).hexdigest().encode()


def build_compact_map(map_path, out_path):


    import marshal
    from array import array
    raw = Path(map_path).read_bytes()
    m = json.loads(gzip.decompress(raw).decode("utf-8"))
    c = dict(m)
    c["sets"] = [array("I", s).tobytes() for s in m["sets"]]
    c["lines"] = {f: (array("I", [int(ln) for ln in d]).tobytes(), array("I", list(d.values())).tobytes())
                  for f, d in m["lines"].items()}
    Path(out_path).parent.mkdir(parents=True, exist_ok=True)
    Path(out_path).write_bytes(_map_digest(raw) + marshal.dumps(c))


def _load_map_json(path):


    import pickle
    raw = Path(path).read_bytes()
    try:
        cached = (CACHE / (Path(path).name + ".pickle")).read_bytes()
        if cached[:40] == _map_digest(raw):
            return pickle.loads(cached[40:])
    except Exception:
        pass
    return json.loads(gzip.decompress(raw).decode("utf-8"))


class _LazyE2(dict):

    def __init__(self, load):
        super().__init__()
        self._load = load

    def _fill(self):
        if self._load is not None:
            load, self._load = self._load, None
            m = load()
            if m is None:
                raise RuntimeError("E2 map unavailable")
            self.update(m)

    def __missing__(self, key):
        if self._load is None:
            raise KeyError(key)
        self._fill()
        return self[key]

    def get(self, key, default=None):
        self._fill()
        return super().get(key, default)


class _LazyCutoff:

    def __init__(self, tests):
        self.tests, self._c = tests, None

    def full(self):

        if self._c is None:
            try:
                import e1_cutoff
                self._c = e1_cutoff.Cutoff(APP / "e1map.json.gz", _load_map_json(APP / "e1map.json.gz"))
            except Exception:
                self._c = False
        return self._c or None

    def droppable(self, src_root, patched_files, wants):
        if self._c is None:
            try:
                import e1_cutoff
                self._c = e1_cutoff.Cutoff(APP / "e1map.json.gz", _load_map_json(APP / "e1map.json.gz"))
            except Exception:
                self._c = False
        return self._c.droppable(src_root, patched_files, wants) if self._c else {}


def _load_map_head(path):


    import pickle
    try:
        cached = (CACHE / (Path(path).name + ".head.pickle")).read_bytes()
        if cached[:40] == _map_digest(Path(path).read_bytes()):
            return pickle.loads(cached[40:])
    except Exception:
        pass
    return None


def build_map_pickle(path):
    import pickle
    raw = Path(path).read_bytes()
    m = json.loads(gzip.decompress(raw).decode("utf-8"))
    CACHE.mkdir(parents=True, exist_ok=True)
    head = {"tests": list(m["tests"]), "missing": list(m.get("missing", ()))}
    (CACHE / (Path(path).name + ".head.pickle")).write_bytes(_map_digest(raw) + pickle.dumps(head, protocol=pickle.HIGHEST_PROTOCOL))
    (CACHE / (Path(path).name + ".pickle")).write_bytes(_map_digest(raw) + pickle.dumps(m, protocol=pickle.HIGHEST_PROTOCOL))


def _load_compact_map(map_path):

    import marshal
    try:
        cached = (CACHE / "map.bin").read_bytes()
        if cached[:40] != _map_digest(Path(map_path).read_bytes()):
            return None
        return marshal.loads(cached[40:])
    except Exception:
        return None


class _LazySets:
    def __init__(self, packed, idx_to_num):
        self.packed, self.idx, self.done = packed, idx_to_num, {}

    def __getitem__(self, sid):
        v = self.done.get(sid)
        if v is None:
            from array import array
            idx = self.idx
            if sid < 0:
                sid += len(self.packed)
            v = self.done[sid] = frozenset(idx[i] for i in array("I", self.packed[sid]) if idx[i] is not None)
        return v


class _LazyLines:
    def __init__(self, packed):
        self.packed, self.done = packed, {}

    def get(self, path, default=None):
        v = self.done.get(path)
        if v is None:
            p = self.packed.get(path)
            if p is None:
                return default
            from array import array
            v = self.done[path] = dict(zip(array("I", p[0]), array("I", p[1])))
        return v





def lpt_cost(ms, chosen):


    import heapq
    if not chosen:
        return 0
    order = sorted((ms[n] for n in chosen), reverse=True)
    best = None
    for k in range(1, min(MAX_WORKERS, len(order)) + 1):
        if best is not None and order[0] + WORKER_COST_MS * k >= best:
            break
        loads = [0] * k
        for x in order:
            heapq.heapreplace(loads, loads[0] + x)
        cost = max(loads) + WORKER_COST_MS * k
        if best is None or cost < best:
            best = cost
    return best


def _pack_cost(ms, chosen):
    bins = lpt_pack(ms, chosen)
    return max((sum(ms[n] for n in b) for b in bins), default=0) + WORKER_COST_MS * len(bins)


def lpt_pack(ms, chosen):

    if not chosen:
        return []
    order = sorted(chosen, key=lambda n: (-ms[n], n))
    best = None
    for k in range(1, min(MAX_WORKERS, len(order)) + 1):
        loads, bins = [0] * k, [[] for _ in range(k)]
        for n in order:
            j = loads.index(min(loads))
            bins[j].append(n)
            loads[j] += ms[n]
        cost = max(loads) + WORKER_COST_MS * k
        if best is None or cost < best[0]:
            best = (cost, bins)
    return best[1]




R1 = os.environ.get("RWX_R1", "1") == "1"
R1_MODE = os.environ.get("RWX_R1_MODE", "empty")
R1_MAP = Path(os.environ.get("RWX_R1_MAP", APP / "r1map.json.gz"))
_R1_OPS = [ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE, ast.Is, ast.IsNot, ast.In, ast.NotIn]


_R1_DEF = re.compile(r"^([ \t]*)(?:async[ \t]+)?def[ \t]")


def _indent(line):
    return len(line) - len(line.lstrip())


def operator_swaps(old_text, new_text):


    ol, nl = old_text.split("\n"), new_text.split("\n")
    if len(ol) == len(nl):
        changed = [i for i in range(len(ol)) if ol[i] != nl[i]]
        if changed:
            i0 = changed[0]
            j = i0
            while j >= 0:
                m = _R1_DEF.match(ol[j])
                if m and len(m.group(1)) < _indent(ol[i0]):
                    break
                j -= 1
            if j >= 0:
                ind = _indent(ol[j])
                k = j + 1
                while k < len(ol) and (not ol[k].strip() or _indent(ol[k]) > ind):
                    k += 1
                if changed[-1] < k:
                    pre = "if 1:\n" if ind else ""
                    r = operator_swaps_in(pre + "\n".join(ol[j:k]), pre + "\n".join(nl[j:k]), j - (1 if pre else 0))
                    if r != "err":
                        return r
    r = operator_swaps_in(old_text, new_text)
    return None if r == "err" else r


def operator_swaps_in(old_text, new_text, line_off=0):



    try:
        o, n = _parse(old_text), _parse(new_text)
    except (SyntaxError, ValueError):
        return "err"
    on, nn = list(ast.walk(o)), list(ast.walk(n))
    if len(on) != len(nn):
        return None
    swaps = []
    for a, b in zip(on, nn):
        if type(a) is not type(b):
            if (isinstance(a, ast.cmpop) and isinstance(b, ast.cmpop)) or (
                    isinstance(a, ast.boolop) and isinstance(b, ast.boolop)):
                continue
            return None
        if getattr(a, "lineno", None) != getattr(b, "lineno", None) or getattr(a, "end_lineno", None) != getattr(b, "end_lineno", None):
            return None
        for f in a._fields:
            va, vb = getattr(a, f, None), getattr(b, f, None)
            if isinstance(va, list):
                if not isinstance(vb, list) or len(va) != len(vb):
                    return None
                if [type(x) if isinstance(x, ast.AST) else ("v", x) for x in va] != [
                        type(x) if isinstance(x, ast.AST) else ("v", x) for x in vb]:
                    if not all(isinstance(x, (ast.cmpop, ast.boolop)) for x in va + vb):
                        return None
            elif not isinstance(va, ast.AST) and va != vb:
                return None
        key = (f"{a.lineno + line_off}:{a.col_offset}:{a.end_lineno + line_off}:{a.end_col_offset}"
               if hasattr(a, "lineno") else None)
        if isinstance(a, ast.Compare) and [type(x) for x in a.ops] != [type(x) for x in b.ops]:
            if len(a.ops) != 1:
                return None
            swaps.append(("c", key, _R1_OPS.index(type(b.ops[0]))))
        elif isinstance(a, ast.BoolOp) and type(a.op) is not type(b.op):
            swaps.append(("b", key, 0 if isinstance(b.op, ast.And) else 1))
    return swaps or None


_SWAP_TOKENS = re.compile(r"\b(?:and|or|is|not|in)\b|==|!=|<=|>=|<|>|\s+")


def maybe_operator_swap(hunks):


    for _os, _ol, _ns, _nl, body in hunks:
        rem = [l[1:] for l in body if l.startswith("-")]
        add = [l[1:] for l in body if l.startswith("+")]
        if not rem or len(rem) != len(add):
            return False
        for r, n in zip(rem, add):
            if r == n or _SWAP_TOKENS.sub("", r) != _SWAP_TOKENS.sub("", n):
                return False
    return True


class WitnessMap:
    def __init__(self, path, number):
        self.path, self.number, self.loaded = path, number, False

    def _load(self):
        self.loaded = True
        self.sets, self.sites = [], {}
        number = self.number
        m = _load_map_json(self.path)
        idx = [number.get(t) for t in m["tests"]]
        self.sets = [frozenset(idx[i] for i in s if idx[i] is not None) for s in m["sets"]]
        self.sites = m["sites"]
        self.skipped = {f: set(v) for f, v in m["skipped"].items()}
        self.missing = {number[t] for t in m["missing"] if t in number}

    def select(self, path, swaps):

        if not self.loaded:
            self._load()
        d = self.sites.get(path)
        if d is None:
            return None
        out = set()
        for kind, key, new_op in swaps:
            s = d.get(key)
            if s is None or s[0] != kind:
                return None
            k, op, ex, alts, col = s
            bit = 1 << (new_op + 1) if kind == "c" else 2
            if col & bit:
                return None
            sid = alts.get(str(new_op if kind == "c" else 0), ex)
            out |= self.sets[sid]
        return out


class Selector:
    def __init__(self, map_path, tests):
        m = _load_compact_map(map_path)
        self.number = {t["id"]: t["number"] for t in tests}

        self.ms = {t["number"]: math.floor(t["seconds"] * 1000 + 0.5) for t in tests}
        self.insurance = []
        self.all = set(self.ms)
        idx_to_num = [self.number.get(t) for t in (m or {}).get("tests", ())]
        if m is not None:
            self.sets = _LazySets(m["sets"], idx_to_num)
            self.lines = _LazyLines(m["lines"])
        else:
            with gzip.open(map_path, "rt", encoding="utf-8") as fh:
                m = json.load(fh)
            idx_to_num = [self.number.get(t) for t in m["tests"]]
            self.sets = [frozenset(idx_to_num[i] for i in s if idx_to_num[i] is not None) for s in m["sets"]]
            self.lines = {f: {int(ln): sid for ln, sid in d.items()} for f, d in m["lines"].items()}
        self.opened = m["opened"]
        self.collect = {f: set(v) for f, v in m["collect"].items()}
        self.classes = m.get("classes", {})
        self.importers = m.get("importers", {})
        traced_ids = set(m["tests"]) - set(m["missing"])
        self.untraced = {t["number"] for t in tests if t["id"] not in traced_ids}
        self.e1, self.e1_nums, self.e1_ids, self.e1_spent = None, set(), {}, 0.0
        self.e1s_spent = 0.0
        self._diff_cache = {}
        if E1 and (APP / "e1map.json.gz").exists():
            try:
                head = _load_map_head(APP / "e1map.json.gz")
                if head is not None:
                    self.e1 = _LazyCutoff(head["tests"])
                else:
                    import e1_cutoff
                    self.e1 = e1_cutoff.Cutoff(APP / "e1map.json.gz", _load_map_json(APP / "e1map.json.gz"))
                self.e1_ids = {self.number[t]: t for t in self.e1.tests if t in self.number}
                self.e1_nums = set(self.e1_ids)
            except Exception:
                self.e1, self.e1_nums, self.e1_ids = None, set(), {}
        self.r1 = WitnessMap(R1_MAP, self.number) if R1 and R1_MAP.exists() else None
        self.by_file = {}
        for t in tests:
            self.by_file.setdefault(t["file"], set()).add(t["number"])
        self._texts, self._scope_names, self._names_memo = {}, None, {}
        self._func_imports, self._openers, self._started = None, None, None
        self.e2 = None
        self.order_groups, self.order_hit = [], False
        if ORDER and ORDER_STATE.exists():
            try:
                for g in json.loads(ORDER_STATE.read_text(encoding="utf-8"))["groups"]:
                    rd = frozenset(self.number[t] for t in g["readers"] if t in self.number)
                    if g["spans"] and rd:
                        self.order_groups.append((g["mutator"], g["owner"] + "." + g["attr"], g["spans"], rd))
            except Exception as e:
                self.order_groups = []
                log(f"order state not loaded ({type(e).__name__}: {e})")
        if E2:
            try:
                self.e2 = self._e2_load()
            except Exception as e:
                log(f"E2 map not loaded ({type(e).__name__}: {e})")


    def _e2_load(self):
        if not (E2_MAP.exists() and E2_FP.exists() and E2_CANON.exists()):
            return None
        head = _load_map_head(E2_MAP)
        if head is not None:
            if set(head["tests"]) != set(self.number) or head["missing"]:
                log("E2 map does not cover this suite: off")
                return None
            return _LazyE2(self._e2_full)
        return self._e2_full()

    def _e2_full(self):
        m = _load_map_json(E2_MAP)
        if set(m["tests"]) != set(self.number) or m["missing"]:
            log("E2 map does not cover this suite: off")
            return None
        m["idx"] = [self.number[t] for t in m["tests"]]
        m["canon"] = set(json.loads(E2_CANON.read_text(encoding="utf-8")))
        m["skipped"] = set(m["skipped"])
        m["_sets"] = {}
        return m

    def _e2_set(self, sid):
        e = self.e2
        s = e["_sets"].get(sid)
        if s is None:
            idx = e["idx"]
            s = e["_sets"][sid] = frozenset(idx[i] for i in e["sets"][sid])
        return s

    def _e2_attr_readers(self, cn, attr):



        e = self.e2
        out = set()
        for recv, sid in e["attr"].get(attr, {}).items():
            if recv not in e["canon"] or cn in e["mro"].get(recv, ()):
                out |= self._e2_set(sid)
        return out

    def _e2_table_readers(self, oid, keys):
        e = self.e2
        out = set()
        if oid in e["whole"]:
            out |= self._e2_set(e["whole"][oid])
        byk = e["key"].get(oid, {})
        for k in keys:
            if k in byk:
                out |= self._e2_set(byk[k])
        return out

    def _e2_global_readers(self, mod, name):


        e = self.e2
        out = set()
        md = e["mod"].get(mod, {})
        for n in (name, "__dict__", "__getattr__", "__all__"):
            if n in md:
                out |= self._e2_set(md[n])
        rel = _mod_file(mod)
        for ln in e["gread"].get(rel, {}).get(name, ()) if rel else ():
            out |= self.touching(rel, ln, ln)
        return out, rel is not None

    def _e2_func_readers(self, metas):
        out = set()
        pre = str(SRC).replace("\\", "/").rstrip("/") + "/"
        for fn, lo, hi, _ in metas:
            fn = fn.replace("\\", "/")
            if not fn.startswith(pre):
                return None
            out |= self.touching(fn[len(pre):], lo, hi)
        return out

    def e2_change_readers(self, ch):

        loc, keys, status, ma, mb, ha, hb, override = ch
        e = self.e2
        oid = e["locs"].get(loc)
        cls_valued = any(isinstance(h, str) and h.startswith("T:") for h in (ha, hb))
        func = ma is not None or mb is not None
        if func and (status != "changed" or ma is None or mb is None):
            func = None
        dele = None
        if L2 and func is None and status == "removed" and ma is not None and not cls_valued:
            dele = next((d for d in _E2_DELS.values() if loc in d), None)
        if loc.startswith("C|"):
            _, cn, attr = loc.split("|", 2)
            if attr.startswith("__") and attr.endswith("__") and attr != "__doc__":
                return None
            if dele is not None and f"C|{cn}|*" not in e["skipped"]:
                return self.deletion_readers(loc, span=self._del_span(loc))
            if f"C|{cn}|*" in e["skipped"] or cls_valued or func is None:
                return None
            if func:
                return self._e2_func_readers(ma)
            if loc in e["skipped"]:
                return None
            if status == "added":


                base = f"C|{override}|{attr}" if override else None
                if base is None or base not in e["locs"] or base in e["skipped"]:
                    return None
            if keys is not None and oid is not None:
                return self._e2_table_readers(oid, keys)
            return self._e2_attr_readers(cn, attr)
        _, mod, name = loc.split("|", 2)
        if f"G|{mod}|*" in e["skipped"] or (name.startswith("__") and name.endswith("__") and name != "__all__"):
            return None
        if dele is not None:
            return self.deletion_readers(loc, span=self._del_span(loc))
        if func:
            return self._e2_func_readers(ma)
        if keys is not None and oid is not None and status == "changed":
            return self._e2_table_readers(oid, keys)
        if cls_valued:
            return None
        out, ok = self._e2_global_readers(mod, name)
        return out if ok else None

    @staticmethod
    def _del_span(loc):
        for path, d in _E2_DELS.items():
            if loc in d:
                return path, d[loc][1], d[loc][2]
        return None

    def deletion_readers(self, loc, metas=None, span=None, failed=()):






        kind, owner, name = loc.split("|", 2)
        if span is None and metas is None:
            return None
        if metas is not None:
            out = self._e2_func_readers(metas)
            if out is None:
                return None
        else:
            out = self.touching(*span)
        if kind == "G":
            g, ok = self._e2_global_readers(owner, name)
            rel = _mod_file(owner)
            if not ok or rel is None:
                return None
            out |= g
        refs = self.name_refs()
        if refs is None or refs.get("*unparsed"):
            return None
        for f, lo, hi, in_func in refs.get(name, ()):
            if _mod_name(f) in failed:
                continue
            if in_func:
                out |= self.touching(f, lo, hi)
            elif f.startswith("tests/"):
                out |= self.by_file.get(f, set()) | self.touching(f)
            else:
                out |= self.file_tests(f) | self.class_users(f, "<module>")
        return out

    def _l2_fallback(self, e2_fb, e2_expect, failed):






        out, kept, n_del = set(), 0, 0
        for p, fb in e2_fb.items():
            if _mod_name(p) in failed:
                continue
            d, ex = _E2_DELS.get(p), e2_expect.get(p)
            r = None
            if d and ex is not None and not ex[1] and ex[0] == set(d):
                r = set()
                for loc, (_, lo, hi) in d.items():
                    x = self.deletion_readers(loc, span=(p, lo, hi), failed=failed)
                    if x is None:
                        r = None
                        break
                    r |= x
            if r is None:
                out |= fb
                kept += 1
            else:
                out |= r
                n_del += 1
        return out, (f"L2: fallback {len(out)} (modules failing: {len(e2_fb) - kept - n_del}, "
                     f"deletions: {n_del}, kept: {kept})")

    def test_helper_defs(self):


        if getattr(self, "_tdefs", None) is None:
            pat = re.compile(r"^\s*(?:async\s+)?def\s+(\w+)", re.M)
            self._tdefs = set()
            for p in (SRC / "tests").rglob("*.py"):
                try:
                    self._tdefs |= set(pat.findall(p.read_text(encoding="utf-8")))
                except (OSError, ValueError):
                    self._tdefs.add("*")
        return self._tdefs

    def name_refs(self):
        if getattr(self, "_refs", None) is None:
            try:
                self._refs = json.loads((CACHE / "name_refs.json").read_text(encoding="utf-8"))
            except (OSError, ValueError):
                self._refs = _ref_index()
        return self._refs

    def e2_readers(self, e2_files, expect=None, add_only=False, both=False):


        import subprocess
        import tempfile
        mods = {}
        for rel, text in e2_files.items():
            name = rel[:-3].replace("/", ".")
            is_pkg = name.endswith(".__init__")
            if is_pkg:
                name = name[: -len(".__init__")]
            mods[name] = [text, is_pkg, str(SRC / rel).replace("\\", "/")]
        out = self._diff_cache.get(json.dumps(mods, sort_keys=True))
        if out is None:
            with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8") as fh:
                json.dump({"patched": mods}, fh)
                tmp = fh.name
            try:
                text = _E2_SERVER.run(tmp, E2_TIMEOUT_S)
                if text is None:
                    text = subprocess.run([sys.executable, "-I", "-S", str(APP / "e2_ns.py"), "diff", str(SRC), str(E2_FP), tmp],
                                          capture_output=True, text=True, timeout=E2_TIMEOUT_S,
                                          env={**os.environ, "PYTHONHASHSEED": "0"}, cwd=tempfile.gettempdir()).stdout
                out = json.loads(text.strip().splitlines()[-1])
            except Exception as ex:
                return (None, f"diff failed ({type(ex).__name__})") + ((set(),) if both else ())
            finally:
                os.unlink(tmp)
            self._diff_cache = {json.dumps(mods, sort_keys=True): out}
        if "error" in out:
            return (None, "diff error: " + out["error"][:200]) + ((set(),) if both else ())

        fail = None
        if out.get("opaque") and not add_only:
            fail = f"opaque value in a patched module: {out['opaque'][0]}"
        self.e2_loadset = out.get("loadset")
        if out.get("loadset") and not add_only:




            fail = f"import-time module loads differ: {out['loadset'][:120]}"
        changed = {c[0] for c in out["changes"]}
        for exact, prefixes in (expect or {}).values() if not add_only and fail is None else ():
            miss = sorted(exact - changed) + sorted(p for p in prefixes if not any(c.startswith(p) for c in changed))
            if miss:
                fail = f"edit not seen by the diff: {miss[0]}"
                break
        sel = set()
        for ch in out["changes"]:
            r = self.e2_change_readers(ch)
            if r is None:
                if fail is None and not add_only:
                    fail = f"unmapped change {ch[0]} ({ch[2]})"
                continue
            sel |= r
            if os.environ.get("RWX_E2_DEBUG"):
                log(f"  E2 {ch[0]} {ch[2]} keys={ch[1]} -> {len(r)}")



        for vals in out.get("strvals", {}).values():
            for v in vals:
                for f in self._e2_modules_named(v):
                    r = self.file_tests(f) | self.class_users(f, "<module>")
                    sel |= r
                    if os.environ.get("RWX_E2_DEBUG"):
                        log(f"  E2 lazy-import table names {f} -> {len(r)}")
        if both:
            return (None if fail else sel), (fail or f"{len(out['changes'])} namespace changes"), sel
        if fail and not add_only:
            return None, fail
        return sel, f"{len(out['changes'])} namespace changes"

    def _e2_modules_named(self, v):

        if not v or len(v) > 80 or not all(p.isidentifier() for p in v.split(".")):
            return []
        if "." in v:
            rel = _mod_file(v)
            return [rel] if rel else []
        idx = getattr(self, "_stem_index", None)
        if idx is None:
            idx = self._stem_index = {}
            for f in (SRC / "sqlglot").rglob("*.py"):
                idx.setdefault(f.stem, []).append(f.relative_to(SRC).as_posix())
        return idx.get(v, [])

    def text(self, path):
        v = self._texts.get(path)
        if v is None:
            try:
                v = (SRC / path).read_text(encoding="utf-8")
            except (OSError, ValueError):
                v = ""
            self._texts[path] = v
        return v

    def import_names(self, path):


        import hashlib
        hit = self._names_memo.get(path, 0)
        if hit != 0:
            return hit
        if self._scope_names is None:
            try:
                self._scope_names = json.loads((CACHE / "import_names.json").read_text(encoding="utf-8"))
            except (OSError, ValueError):
                self._scope_names = {}
        text = self.text(path)
        e = self._scope_names.get(path)
        digest = hashlib.sha1(text.encode("utf-8", "surrogatepass")).hexdigest()
        if not (isinstance(e, list) and e[0] == digest):
            try:
                e = [digest, sorted(import_scope_names(text))]
            except (SyntaxError, ValueError):
                e = [digest, None]
            self._scope_names[path] = e
        v = self._names_memo[path] = None if e[1] is None else set(e[1])
        return v

    def name_readers(self, path, names):




        if not names:
            return set()
        pat = re.compile(r"\b(?:" + "|".join(map(re.escape, sorted(names))) + r")\b")
        out = set()
        for f in self.import_closure(path) - {path}:
            if not f.endswith(".py") or not pat.search(self.text(f)):
                continue
            if f in self.by_file:
                out |= self.by_file[f]
            try:
                reads = name_reads(self.text(f), names)
            except (SyntaxError, ValueError):
                reads = None
            if reads is None:
                out |= self.file_tests(f) | self.class_users(f, "<module>")
                continue
            for lo, hi in reads:
                out |= self.touching(f, lo, hi)
        return out

    def lazy_import_users(self, path, fname):



        out = set()
        for f in {path, *self.importers.get(path, ())}:
            if f.endswith(".py") and f not in self.collect:
                n = self.import_names(f)
                if n is None or fname in n:
                    out |= self.file_tests(f) | self.class_users(f, "<module>")
        return out

    def package_tests(self, path):

        pre = path.rsplit("/", 1)[0] + "/"
        out = set()
        for f, nums in self.by_file.items():
            if f.startswith(pre):
                out |= nums
        return out

    def dir_openers(self, path):


        parent = path.rsplit("/", 1)[0] if "/" in path else ""
        out = set()
        for k, sid in self.opened.items():
            kp = k.rsplit("/", 1)[0] if "/" in k else ""
            if (k != path and kp == parent) or path.startswith(k.rstrip("/") + "/"):
                out |= self.sets[sid]
        return out

    def dir_mentions(self, path):


        top = path.split("/", 1)[0]
        if "/" not in path or top == "tests" or (SRC / top / "__init__.py").exists():
            return set()
        pat = re.compile(r"\b" + re.escape(top) + r"\b")
        out = set()
        for f, nums in self.by_file.items():
            if pat.search(self.text(f)):
                out |= nums
        return out

    def touching(self, path, lo=None, hi=None):
        d = self.lines.get(path, {})
        out = set()
        seen = set()
        for ln, sid in d.items():
            if (lo is None or ln >= lo) and (hi is None or ln <= hi) and sid not in seen:
                seen.add(sid)
                out |= self.sets[sid]
        return out

    def class_users(self, path, qualname):

        mod = path[:-3].replace("/", ".")
        if mod.endswith(".__init__"):
            mod = mod[: -len(".__init__")]
        out = set()
        if qualname == "<module>":
            pre = mod + ":"
            for c, sid in self.classes.items():
                if c.startswith(pre):
                    out |= self.sets[sid]
        else:
            sid = self.classes.get(f"{mod}:{qualname}")
            if sid is not None:
                out |= self.sets[sid]
        return out

    def import_closure(self, path):

        seen, todo = {path}, [path]
        while todo:
            for imp in self.importers.get(todo.pop(), ()):
                if imp not in seen:
                    seen.add(imp)
                    todo.append(imp)
        return seen

    def broken_module_tests(self, paths):



        files = set()
        for p in paths:
            files |= self.import_closure(p)
        if "sqlglot/__init__.py" in files or any(f in self.collect for f in files):
            return set(self.all), files
        sel = set()
        for f in files:
            sel |= self.file_tests(f) | self.class_users(f, "<module>")
        return sel, files

    def func_import_users(self, path):


        if self._func_imports is None:
            try:
                self._func_imports = json.loads((CACHE / "func_imports.json").read_text(encoding="utf-8"))
            except (OSError, ValueError):
                self._func_imports = _func_import_index()
        out = set()
        for imp, lo, hi in self._func_imports.get(path, ()):
            out |= self.touching(imp, lo, hi)
        return out

    def collection_broken(self, patched):






        try:
            base = _baseline_full()
            order = _full_probe_files()
            order += sorted(set(patched) - set(order))
            failed, detail = import_fails(SRC, patched, order, baseline=base, in_order=True)
        except Exception:
            return None
        if not failed or detail == "timeout" or detail.startswith("probe crashed"):
            return None
        names = set(detail.split(", "))
        if "sqlglot" in names:
            return set(self.all), names
        tm = set(test_modules())
        sel = set()
        for name in names:
            for rel in (name.replace(".", "/") + ".py", name.replace(".", "/") + "/__init__.py"):
                if (SRC / rel).exists() or rel in patched:
                    break
            else:
                return None
            if rel in tm:
                sel |= self.by_file.get(rel, set())
            else:
                sel |= self.file_tests(rel) | self.class_users(rel, "<module>") | self.func_import_users(rel)
        for f, nums in self.by_file.items():
            if f not in tm or _mod_name(f) in base:
                sel |= nums
        return sel, names

    def loader_invisible(self, path, old_text, new_text, patched_paths):




        if self._openers is None:
            try:
                self._openers = json.loads((APP / "fixture_openers.json").read_text(encoding="utf-8"))
            except (OSError, ValueError):
                self._openers = {}
        r = self._loader_entries(path, old_text, new_text, patched_paths)
        return r is not None and r[1] == r[2]

    def _loader_entries(self, path, old_text, new_text, patched_paths):

        if self._openers is None:
            try:
                self._openers = json.loads((APP / "fixture_openers.json").read_text(encoding="utf-8"))
            except (OSError, ValueError):
                self._openers = {}
        who = self._openers.get(path)
        helper = "tests/helpers.py"
        if not who or helper in patched_paths or any(not w.startswith(helper + ":") for w in who):
            return None
        import io
        try:
            ns = {"__name__": "rwx_fixture_helpers", "__file__": str(SRC / helper)}
            exec(compile(self.text(helper), str(SRC / helper), "exec"), ns)

            def entries(text):
                ns["open"] = lambda *a, **k: io.StringIO(text, newline=None)
                return [list(ns[w.split(":", 1)[1]](path)) for w in sorted(who)]
            return sorted(w.split(":", 1)[1] for w in who), entries(old_text), entries(new_text)
        except Exception:
            return None

    def meta_invisible(self, path, old_text, new_text, patched_paths):







        if any(p.startswith("tests/") and p.endswith(".py") for p in patched_paths):
            return False
        r = self._loader_entries(path, old_text, new_text, patched_paths)
        if r is None:
            return False
        names, olds, news = r
        diff_keys, pos = set(), set()
        missing = object()
        for eo, en in zip(olds, news):
            if len(eo) != len(en):
                return False
            for a, b in zip(eo, en):
                if a == b:
                    continue
                if not (isinstance(a, tuple) and isinstance(b, tuple) and len(a) == len(b)):
                    return False
                for i, (x, y) in enumerate(zip(a, b)):
                    if x == y:
                        continue
                    if not (isinstance(x, dict) and isinstance(y, dict)):
                        return False
                    pos.add(i)
                    diff_keys |= {k for k in set(x) | set(y) if x.get(k, missing) != y.get(k, missing)}
        if not diff_keys or len(pos) != 1:
            return False
        fx = path[len("tests/fixtures/"):] if path.startswith("tests/fixtures/") else None
        read = self._meta_keys_read(set(names), pos.pop(), fx)
        return read is not None and not (read & diff_keys)

    def _meta_keys_read(self, loaders, pos, fx):


        read = set()
        for p in sorted((SRC / "tests").rglob("*.py")):
            rel = p.relative_to(SRC).as_posix()
            text = self.text(rel)
            if not any(w in text for w in loaders):
                continue
            try:
                tree = ast.parse(text)
            except (SyntaxError, ValueError):
                return None
            parent = {}
            for n in ast.walk(tree):
                for ch in ast.iter_child_nodes(n):
                    parent[id(ch)] = n
            for n in ast.walk(tree):
                if isinstance(n, (ast.Name, ast.Attribute, ast.alias)):
                    nm = n.id if isinstance(n, ast.Name) else n.attr if isinstance(n, ast.Attribute) else (n.asname or n.name)
                    pa = parent.get(id(n))
                    if nm in loaders and not (isinstance(pa, ast.ImportFrom) or (isinstance(pa, ast.Call) and pa.func is n)):
                        return None
                    if isinstance(n, ast.alias) and n.asname and n.name in loaders:
                        return None
            for call in ast.walk(tree):
                if not isinstance(call, ast.Call):
                    continue
                fn = call.func.id if isinstance(call.func, ast.Name) else getattr(call.func, "attr", None)
                if fn not in loaders:
                    continue
                if rel == "tests/helpers.py":
                    return None
                arg = call.args[0] if call.args else None
                if fx is not None and isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                    if arg.value != fx:
                        continue
                elif fx is not None and isinstance(arg, ast.JoinedStr):
                    pat = "".join(re.escape(v.value) if isinstance(v, ast.Constant) else ".*" for v in arg.values)
                    if not re.fullmatch(pat, fx, re.S):
                        continue
                up = parent.get(id(call))
                node = call
                if (isinstance(up, ast.Call) and isinstance(up.func, ast.Name) and up.func.id == "enumerate"
                        and up.args and up.args[0] is call):
                    node, up = up, parent.get(id(up))
                if not (isinstance(up, ast.For) and up.iter is node):
                    return None
                tg = up.target
                if node is not call:
                    if not (isinstance(tg, ast.Tuple) and len(tg.elts) == 2):
                        return None
                    tg = tg.elts[1]
                if not (isinstance(tg, ast.Tuple) and len(tg.elts) > pos and isinstance(tg.elts[pos], ast.Name)):
                    return None
                m = tg.elts[pos].id
                scope = _enclosing_def(up, parent) or tree
                for n in ast.walk(scope):
                    if not (isinstance(n, ast.Name) and n.id == m) or n is tg.elts[pos]:
                        continue
                    pa = parent.get(id(n))
                    if (isinstance(pa, ast.Subscript) and pa.value is n and isinstance(pa.ctx, ast.Load)
                            and isinstance(pa.slice, ast.Constant)):
                        read.add(pa.slice.value)
                        continue
                    if isinstance(pa, ast.Attribute) and pa.attr == "get":
                        c = parent.get(id(pa))
                        if isinstance(c, ast.Call) and c.func is pa and c.args and isinstance(c.args[0], ast.Constant):
                            read.add(c.args[0].value)
                            continue
                    return None
        return read

    def import_inert(self, path, old_text, regions):




        import hashlib
        if self._started is None:
            try:
                self._started = json.loads((CACHE / "import_started.json").read_text(encoding="utf-8"))
            except (OSError, ValueError):
                self._started = {}
        st = self._started.get(path)
        if not st or "<module>" not in st or not regions:
            return False
        if old_text != self.text(path):
            return False
        names = set(st)
        for kind, _, qualname, _, _ in regions:
            if kind != "func" or qualname in names or any(n.startswith(qualname + ".") for n in names):
                return False
        return True

    def file_tests(self, path):
        sel = self.touching(path)
        if path in self.opened:
            sel |= self.sets[self.opened[path]]
        sel |= self.by_file.get(path, set())
        return sel

    def select(self, patch_text, allow_probe=True, raw=None):
        why = []
        self.order_hit = False


        self.insurance = tiers = [set(), set(), set()]
        try:
            files = parse_patch(patch_text)
        except Exception as e:
            return set(self.all), [f"unparseable patch: {e}"]
        if not files:
            return set(), ["empty patch"]
        patched_paths = {p for f in files for p in (f["old"], f["new"]) if p}


        raw_clean = _raw_clean_paths(raw) if raw is not None else set()
        chosen = set()
        e2_fallback, e2_files, e2_block, e2_expect = set(), {}, False, {}
        e2_fb = {}
        _E2_DELS.clear()
        order_add = set()
        e2_bind = False
        e2_noprune = False
        e1_soft, e1_files = [], {}

        xs = {"bail": None, "func": [], "scope": [], "fix": {}, "expect": {}}

        def bail(reason):
            if xs["bail"] is None:
                xs["bail"] = reason
        scope_changed = {}
        inert = set()
        for f in files:
            old, new = f["old"], f["new"]
            path = old or new
            if f["binary"]:
                bail("binary")
                chosen |= self.file_tests(path)
                why.append(f"{path}: binary -> file tests")
                continue
            if path in CONFIG_FILES or Path(path).name == "conftest.py":
                why.append(f"{path}: test configuration -> all")
                return set(self.all), why
            if old is None or new is None or new != old:
                e2_block = True
            if old is None:
                bail("new file")
                if importable(new):
                    try:
                        scope_changed[new] = apply_hunks("", f["hunks"])[0]
                    except ValueError:
                        pass
                sel = self.dir_openers(new) | (set() if new.endswith(".py") else self.dir_mentions(new))
                chosen |= sel
                why.append(f"{new}: new file -> directory openers {len(sel)}")
                continue
            src = SRC / old
            if not src.exists():
                bail("not in tree")
                why.append(f"{old}: not in pinned tree -> none")
                continue
            old_text = src.read_text(encoding="utf-8")
            if new is None or new != old:
                bail("deleted or renamed")
            if new is None or (new != old and old.endswith(".py")):

                sel, files_ = self.broken_module_tests([old]) if old.endswith(".py") else (self.file_tests(old), {old})
                chosen |= sel
                why.append(f"{old}: {'deleted' if new is None else 'renamed'} -> {len(sel)}")
                continue
            try:
                new_text, changed, inserts = apply_hunks(old_text, f["hunks"])
            except ValueError as e:
                bail("hunks")
                sel = self.broken_module_tests([old])[0] if old.endswith(".py") else self.file_tests(old)
                chosen |= sel
                why.append(f"{old}: hunks do not apply ({e}) -> {len(sel)}")
                continue
            if new != old:
                chosen |= self.file_tests(old)
            if not old.endswith(".py"):
                if new == old and old in raw_clean and self.loader_invisible(old, old_text, new_text, patched_paths):
                    why.append(f"{old}: data file, its loaders yield the same entries -> none")
                    continue
                if L5 and new == old and old in raw_clean and self.meta_invisible(old, old_text, new_text, patched_paths):
                    why.append(f"{old}: data file, only metadata keys no test reads differ -> none")
                    continue
                if old in E1S_FIXTURES:
                    xs["fix"][E1S_FIXTURES[old]] = new_text
                elif self.e1 and (self.file_tests(old) | self.dir_mentions(old)) & self.e1_nums:
                    bail("data file read by an E1 test")
                sel = set()
                if old in self.opened:
                    sel = set(self.sets[self.opened[old]])
                sel |= self.dir_mentions(old)
                chosen |= sel
                why.append(f"{old}: data file -> openers {len(sel)}")
                continue
            if (L5 and old.startswith("tests/") and Path(old).name.startswith("test_") and old in raw_clean
                    and not any(ln.startswith("+") for h in f["hunks"] for ln in h[4])
                    and (k := assertion_deletions(old_text, new_text, self.test_helper_defs()))):
                why.append(f"{old}: only deletes {k} side-effect-free assertion(s) -> none")
                continue
            status, regions = code_changes(old, old_text, new_text, f["hunks"])
            if status == "changed" and self.import_inert(old, old_text, regions):
                inert.add(old)
            e1_files[old] = new_text
            if status != "null" and not old.startswith("sqlglot/"):
                bail("code outside sqlglot/")
            if status == "syntax":
                bail("syntax")
            if status == "null":
                why.append(f"{old}: bytecode-identical -> none")
                continue
            for mutator, what, spans, rd in self.order_groups:
                ss = spans.get(old, ())
                if any(a <= hi and lo <= b for _, _, _, (lo, hi), _ in regions for a, b in ss):
                    self.order_hit = True
                    order_add |= rd
                    why.append(f"{old}: touches {what}, left mutated by {mutator} -> later readers {len(rd)}")
            if status == "syntax":
                r = self.collection_broken({old: new_text}) if allow_probe and importable(old) else None
                if r is not None:
                    sel, names = r
                    chosen |= sel
                    why.append(f"{old}: syntax error -> collection probe: {len(names)} modules fail: {len(sel)}")
                    continue
                sel, files_ = self.broken_module_tests([old])
                chosen |= sel
                why.append(f"{old}: syntax error -> users of it and its {len(files_) - 1} importers: {len(sel)}")
                continue
            r1_sel = None
            try:
                if self.r1 is not None and old.startswith("sqlglot/") and maybe_operator_swap(f["hunks"]):



                    swaps = operator_swaps(old_text, new_text)
                    r1_sel = self.r1.select(old, swaps) if swaps else None
                    if r1_sel is not None:

                        r1_sel |= self.touching(old) & self.r1.missing
                    if r1_sel and R1_MODE != "partial":


                        why.append(f"{old}: operator swap witnessed by {len(r1_sel)} tests -> regions")
                        r1_sel = None
                    if r1_sel is not None:
                        why.append(f"{old}: {len(swaps)} operator swap(s) -> witnesses {len(r1_sel)}")
            except Exception:
                r1_sel = None
            sel = set() if r1_sel is None else set(r1_sel)
            tiers[1] |= self.file_tests(old)
            tiers[2] |= self.class_users(old, "<module>")
            col = self.collect.get(old, set())
            if regions and importable(old) and old not in self.collect:




                scope_changed[old] = new_text
            narrowed = 0
            e2_ok = E2 and old.startswith("sqlglot/") and self.e2 is not None
            e2_prune = e2_ok and E2_PRUNE




            e2_span = False
            if e2_prune:
                e2_expect[old] = e2_expected(old, old_text, new_text)
                e2_span = e2_expect[old] is not None and not e2_expect[old][1] and not _E2_UNMODELED.get(old)
            for kind, ranges, qualname, (lo, hi), own in regions:
                ran_at_import = kind == "func" and bool(own & col)
                at_import = ran_at_import
                if at_import and FRAME_DIFF and ranges != [(lo, hi)]:


                    at_import = any(a <= ln <= b for ln in col for a, b in ranges)
                    if not at_import and importable(old):
                        scope_changed[old] = new_text
                if kind == "func":
                    xs["func"].append((old, [(lo, hi)] if at_import else list(ranges), (lo, hi)))
                if kind == "scope" or at_import:
                    xs["scope"].append((old, list(ranges) + [(lo, hi)] if kind == "scope" else [(lo, hi)]))
                if at_import or ranges == [(lo, hi)]:


                    ranges = [(lo, hi)]
                else:
                    narrowed += 1
                hit = set()
                for a, b in ranges if r1_sel is None else ():
                    hit |= self.touching(old, a, b)
                if e2_span and kind == "scope" and not at_import:
                    e2_fallback |= hit
                    e2_fb.setdefault(old, set()).update(hit)
                    hit = set()
                if self.e1 and r1_sel is None and kind == "func" and not at_import and old.startswith("sqlglot/"):
                    e1_soft.append((old, ranges, hit & self.e1_nums))
                    hit = hit - self.e1_nums
                sel |= hit
                if ranges != [(lo, hi)]:
                    tiers[0] |= self.touching(old, lo, hi)
                if at_import:
                    if importable(old):
                        scope_changed[old] = new_text
                    if not hit:

                        kind, qualname = "scope", "<module>"
                        sel |= self.touching(old)
                if kind == "func" and "." not in qualname and not at_import:
                    sel |= self.lazy_import_users(old, qualname)
                if kind == "func" and qualname == "__getattr__":



                    sel |= self.func_import_users("lazy:" + old)
                if IMPORT_TIME_RULE and at_import:
                    kind, qualname = "scope", "<module>"
                if kind == "scope":


                    wide = self.class_users(old, qualname)
                    if e2_prune and not at_import:


                        e2_fallback |= wide
                        e2_fb.setdefault(old, set()).update(wide)
                    else:
                        sel |= wide
                    if importable(old):
                        scope_changed[old] = new_text
                    if old.startswith("tests/"):
                        sel |= self.by_file.get(old, set())
            if any(r[0] == "scope" for r in regions):
                try:
                    names, added, effects = top_level_changes(old_text, new_text)
                except (SyntaxError, ValueError):
                    names, added, effects = None, None, True
                if e2_ok and (names is None or names or added):
                    e2_bind = True
                if names is None or effects:
                    bail("module-level effects")
                if old.startswith("sqlglot/"):
                    xs["expect"][old] = e2_expected(old, old_text, new_text)
                    if xs["expect"][old] is None:
                        bail("diff expectation unknown")
                helper = old.startswith("tests/") and not Path(old).name.startswith("test_")
                if helper and effects:


                    why.append(f"{old}: module-level side effect in a test helper -> all")
                    return set(self.all), why
                if names is None:
                    sel |= set(self.all)
                else:
                    if helper and names:
                        sel |= self.package_tests(old)
                    nr = self.name_readers(old, names)
                    if e2_prune:
                        e2_fallback |= nr - sel
                        e2_fb.setdefault(old, set()).update(nr - sel)
                    else:
                        sel |= nr
            chosen |= sel
            if e2_ok:
                e2_files[old] = new_text
                if old not in e2_expect:
                    e2_expect[old] = e2_expected(old, old_text, new_text)
                if e2_expect[old] is None:
                    e2_block = True
                elif _E2_UNMODELED.get(old):
                    e2_noprune = True
            else:
                e2_block = True
            why.append(f"{old}: {len(regions)} changed code regions ({narrowed} statement-level) -> {len(sel)}")
        if scope_changed:



            closure = set()
            for p in scope_changed:
                closure |= self.import_closure(p)
            probe = sorted(f for f in closure if importable(f))
            static_ok = STATIC_IMPORT and all(p in inert for p in scope_changed)
            lazy_w = self._lazy_probe(scope_changed, chosen) if allow_probe and LAZY and not static_ok else None
            if static_ok:
                failed, detail = False, ""
                why.append("import check ok (static: edits never run at import)")
            elif lazy_w is not None:


                chosen |= lazy_w
                failed, detail = False, ""
                why.append(f"import check skipped (lazy): failure set {len(lazy_w)} fits")
            elif allow_probe:
                failed, detail = import_fails(SRC, scope_changed, probe)
            else:
                failed, detail = True, "probe skipped: run deadline"
            if failed:
                bail("import fails")
            if failed and (not allow_probe or detail == "timeout" or detail.startswith("probe crashed")):


                why.append(f"import check gave no verdict ({detail.strip().splitlines()[-1:]}) -> all")
                return set(self.all), why
            if failed:
                broken = {p for p in scope_changed if (SRC / p).exists()}
                for name in detail.split(", ") if allow_probe else ():

                    for rel in (name.replace(".", "/") + ".py", name.replace(".", "/") + "/__init__.py"):
                        if (SRC / rel).exists():
                            broken.add(rel)
                r = self.collection_broken(scope_changed)
                if r is not None:
                    sel, names = r
                    chosen |= sel
                    why.append(f"import fails ({detail.strip().splitlines()[-1:]}) -> collection probe: {len(names)} modules fail: {len(sel)}")
                    if L2 and e2_fb:
                        e2_fallback, l2why = self._l2_fallback(e2_fb, e2_expect, names)
                        why.append(l2why)
                else:
                    sel, files_ = self.broken_module_tests(sorted(broken))
                    chosen |= sel
                    why.append(f"import fails ({detail.strip().splitlines()[-1:]}) -> users of {len(files_)} modules: {len(sel)}")
            elif lazy_w is None and not static_ok:
                why.append("import check ok")
                failed = False
        else:
            failed = False
        if E2 and self.e2 is not None and not E2_PRUNE:

            if e2_bind and not failed and not e2_block and allow_probe and LAZY and self._free(chosen, self.all):
                chosen |= self.all
                why.append("g8 skipped (lazy): every test fits")
            elif e2_bind and not failed and not e2_block and allow_probe:
                e2sel, detail = self.e2_readers(e2_files, e2_expect, add_only=True)
                why.append(f"g8: {detail}")
                if e2sel:
                    chosen |= e2sel
                    why.append(f"g8 adds readers {len(e2sel)}")
        elif E2 and self.e2 is not None and (e2_fallback - chosen or e2_bind):




            e2sel, e2add = None, set()




            gain = self._cost(chosen | e2_fallback) - self._cost(chosen) if e2_fallback - chosen else 0

            unmappable = any(_E2_DEFS.get(f, set()) - set(_E2_DELS.get(f, {}) if L2 else ()) for f in e2_files)
            if (gain < E2_COST_MS or unmappable or e2_noprune) and not e2_bind:
                why.append(f"E2 skipped: at most {gain:.0f} ms to gain" + (", def added or removed" if unmappable else ""))
            elif not failed and not e2_block and allow_probe:
                self.e2_loadset = None
                e2sel, detail, e2add = self.e2_readers(e2_files, e2_expect, both=True)
                why.append(f"E2: {detail}")
                if self.e2_loadset:
                    why.append("E2: import-time module loads differ -> all")
                    chosen |= set(self.all)
                if e2_noprune and e2sel is not None:
                    e2sel = None
                    why.append("E2: import / header edit, readers only added")
            if e2sel is None:
                chosen |= e2_fallback | e2add
                why.append(f"E2 fallback -> {len(e2_fallback)} (+ g8 readers {len(e2add - e2_fallback)})")
            else:
                chosen |= e2sel
                why.append(f"E2 readers {len(e2sel)} instead of {len(e2_fallback)}")
        if xs["scope"] and not E1S_SCOPE:
            bail("namespace edit (RWX_E1S_SCOPE=0)")
        if E1S and self.e1 and self.e2 is not None and xs["bail"] is None and (xs["scope"] or xs["fix"])                 and allow_probe:
            for _, _, tests in e1_soft:
                chosen |= tests
            chosen -= self.e1s_check(xs, e1_files, chosen, why)
        elif e1_soft:
            chosen |= self.e1_check(e1_soft, e1_files, chosen, why)
        if E1S and self.e1 and xs["bail"] is not None and chosen & self.e1_nums:
            why.append(f"E1S off: {xs['bail']}")
        chosen |= order_add
        if chosen and self.untraced:
            chosen |= self.untraced
        return chosen, why

    def _ns_diff(self, files):

        files = {r: t for r, t in files.items() if r.startswith("sqlglot/")}
        key = self._diff_key(files)
        if key not in self._diff_cache:
            self.e2_readers(files, add_only=True)
        out = self._diff_cache.get(key)
        return None if out is None or "error" in out else out

    def _e1s_elines(self, tid, rel):
        C = self.e1.full() if isinstance(self.e1, _LazyCutoff) else self.e1
        return C.tests[tid]["E"].get(rel, ())

    def _lpt(self, sel):
        return lpt_cost(self.ms, sel | self.untraced if sel and self.untraced else sel)

    def _diff_key(self, files):
        mods = {}
        for rel, text in files.items():
            if not rel.startswith("sqlglot/"):
                continue
            name = rel[:-3].replace("/", ".")
            is_pkg = name.endswith(".__init__")
            if is_pkg:
                name = name[: -len(".__init__")]
            mods[name] = [text, is_pkg, str(SRC / rel).replace("\\", "/")]
        return json.dumps(mods, sort_keys=True)

    def _e1s_change_reaches_e(self, ch, tid, xs):




        loc, keys, status, ma, mb, ha, hb, override = ch
        n = self.number[tid]
        if any(isinstance(h, str) and h.startswith("T:") for h in (ha, hb)):
            return True
        kind, owner, name = loc.split("|", 2)
        if name.startswith("__") and name.endswith("__"):
            return True
        if ma is not None or mb is not None:
            if status != "changed" or ma is None or mb is None:
                return True
            pre = str(SRC).replace("\\", "/").rstrip("/") + "/"
            for fn, lo, hi, _ in ma:
                fn = fn.replace("\\", "/")
                if not fn.startswith(pre):
                    return True
                rel = fn[len(pre):]


                body_only = any(r == rel and flo >= lo and fhi <= hi for r, _, (flo, fhi) in xs["func"]) and \
                    not any(r == rel and a <= hi and b >= lo for r, rs in xs["scope"] for a, b in rs)
                if body_only:
                    continue
                if any(lo <= ln <= hi for ln in self._e1s_elines(tid, rel)):
                    return True
            return False
        e = self.e2
        if kind == "C":
            r = self.e2_change_readers(ch)
            return r is None or n in r
        if f"G|{owner}|*" in e["skipped"]:
            return True
        md = e["mod"].get(owner, {})
        for k in (name, "__dict__", "__getattr__", "__all__"):
            if k in md and n in self._e2_set(md[k]):
                return True
        rel = _mod_file(owner)
        if rel is None:
            return True
        gl = set(e["gread"].get(rel, {}).get(name, ()))
        return any(ln in gl for ln in self._e1s_elines(tid, rel))

    def e1s_check(self, xs, files, chosen, why):





        import e1_cutoff
        cands = {self.e1_ids[n] for n in chosen & self.e1_nums}
        if not cands:
            return set()
        C = self.e1.full() if isinstance(self.e1, _LazyCutoff) else self.e1
        if not C:
            return set()
        t0 = time.monotonic()
        rest = chosen - {self.number[t] for t in cands}
        gain = self._lpt(chosen) - self._lpt(rest)
        fixk = {k for k, (f, _) in e1_cutoff.FIXTURE.items() if f in xs["fix"]}
        kinds = {C.tests[t]["kind"] for t in cands}


        diff_ms = 0 if not xs["scope"] or self._diff_key(files) in self._diff_cache else E1S_DIFF_MS
        full = kinds if xs["scope"] or xs["func"] else set()
        cost = diff_ms + E1S_CHILD_MS + sum(E1S_KIND_MS.get(k, 3000) for k in full) + \
            E1S_FIXTURE_MS * len(xs["fix"])
        if gain <= cost:
            why.append(f"E1S skipped: {gain} ms to gain, ~{cost} ms to check")
            return set()
        left = E1S_BUDGET_S - self.e1s_spent
        if cost / 1000 > left:
            why.append(f"E1S skipped: budget ({left:.1f}s left, ~{cost} ms to check)")
            return set()
        keep = set()
        for tid in cands:
            d = C.tests[tid]
            for rel, ranges, _ in xs["func"]:
                ex = d["E"].get(rel, ())
                for a, b in ranges:
                    if any(a <= ln <= b for ln in ex):
                        keep.add(tid)
                    elif self.number[tid] in self.touching(rel, a, b) and \
                            not any(a <= ln <= b for q in d["Q"] for ln in q.get(rel, ())):
                        keep.add(tid)
        live = cands - keep
        if live and xs["scope"]:
            out = self._ns_diff(files)
            reason = None
            if out is None:
                reason = "diff failed"
            elif out.get("opaque"):
                reason = "opaque value"
            elif out.get("strvals"):
                reason = "lazy-import table changed"
            else:
                changed = {c[0] for c in out["changes"]}
                for exact, prefixes in xs["expect"].values():
                    if exact - changed or any(not any(c.startswith(p) for c in changed) for p in prefixes):
                        reason = "edit not seen by the diff"
            if reason is not None:
                why.append(f"E1S: {reason}")
                live = set()
            else:
                dr = self.e2.get("dictread", {})
                for tid in sorted(live):
                    if any(ln in set(v) for rel, v in dr.items() for ln in self._e1s_elines(tid, rel)):
                        keep.add(tid)
                        continue
                    for ch in out["changes"]:
                        if self._e1s_change_reaches_e(ch, tid, xs):
                            keep.add(tid)
                            if os.environ.get("RWX_E2_DEBUG"):
                                log(f"  E1S keeps {tid}: {ch[0]} {ch[2]}")
                            break
                live -= keep
        if live:


            work = {}
            for tid in live:
                k = C.tests[tid]["kind"]
                if xs["scope"]:
                    work[k] = {"idx": "all"}
                    continue

                q = {i for i, ql in enumerate(C.tests[tid]["Q"]) for rel, ranges, _ in xs["func"]
                     for a, b in ranges if any(a <= ln <= b for ln in ql.get(rel, ()))}
                if k in fixk or q:
                    w = work.setdefault(k, {"idx": [], "changed": k in fixk})
                    w["idx"] = sorted(set(w["idx"]) | q)
            got = None
            if work or xs["fix"]:
                expect = {t["kind"]: t["fp"] for t in C.tests.values()}
                got = e1_cutoff.recompute(SRC, {r: x for r, x in files.items() if r.startswith("sqlglot/")},
                                          work, expect=expect, fixtures=xs["fix"])
            for tid in sorted(live):
                d = C.tests[tid]
                k = d["kind"]
                if xs["fix"] and not (got and all(got.get("_fixtures", {}).get(f) for f in xs["fix"])):
                    keep.add(tid)
                    continue
                if k in work:
                    g = (got or {}).get(k, {})
                    idx = g.get("_idx")
                    if g.get("_n") != len(d["fp"]) or idx is None or \
                            (work[k]["idx"] == "all" and len(idx) != len(d["fp"])) or \
                            not all(g.get(str(i)) == d["fp"][i] for i in idx):
                        keep.add(tid)
            live -= keep
        spent = time.monotonic() - t0
        self.e1s_spent += cost / 1000
        why.append(f"E1S {len(live)}/{len(cands)} dropped ({spent:.1f}s, ~{cost} ms, gain {gain} ms): {sorted(live)}")
        return {self.number[t] for t in live}

    def e1_check(self, soft, files, hard, why):


        wants = {}
        for path, ranges, tests in soft:
            for n in tests - hard:
                wants.setdefault(self.e1_ids[n], []).append((path, ranges))
        if not wants:
            return set()
        keep_all = {self.number[tid] for tid in wants}
        if LAZY and self._free(hard, keep_all):
            why.append(f"E1 skipped (lazy): keeping its {len(wants)} tests costs nothing")
            return keep_all


        C = self.e1.full() if isinstance(self.e1, _LazyCutoff) else self.e1
        if not C:
            return keep_all
        plans = {tid: C.plan(tid, regions) for tid, regions in wants.items()}
        plans = {tid: p for tid, p in plans.items() if p is not None}
        if not plans:
            why.append(f"E1 skipped: no plan for its {len(wants)} tests")
            return keep_all
        work = {}
        for tid, p in plans.items():
            work.setdefault(C.tests[tid]["kind"], set()).update(p)
        cost = E1S_CHILD_MS + sum(E1S_KIND_MS.get(k, 3000) * len(q) / max(1, len(next(
            C.tests[t]["fp"] for t in plans if C.tests[t]["kind"] == k))) for k, q in work.items())
        gain = self._lpt(hard | keep_all) - self._lpt(hard | (keep_all - {self.number[t] for t in plans}))
        if gain <= cost:
            why.append(f"E1 skipped: {gain} ms to gain, ~{cost:.0f} ms to check")
            return keep_all
        if self.e1_spent + cost / 1000 > E1_BUDGET_S:
            why.append(f"E1 skipped: budget ({self.e1_spent:.1f}s predicted used, ~{cost:.0f} ms to check)")
            return keep_all
        t = time.monotonic()
        dropped = self.e1.droppable(SRC, files, wants)
        self.e1_spent += cost / 1000
        why.append(f"E1 {len(dropped)}/{len(wants)} dropped ({time.monotonic() - t:.1f}s): {sorted(dropped)}")
        return {self.number[tid] for tid in wants if tid not in dropped}

    def _cost(self, chosen):
        bins = [b for b in lpt_pack(self.ms, chosen) if b] if chosen else []
        return max(sum(self.ms[n] for n in b) for b in bins) + WORKER_COST_MS * len(bins) if bins else 0

    def _free(self, cur, extra):



        extra = set(extra) - cur
        if not extra:
            return True
        base = cur | self.untraced if cur and self.untraced else cur
        wide = base | extra | self.untraced if self.untraced else base | extra
        return lpt_cost(self.ms, wide) <= lpt_cost(self.ms, base)

    def _lazy_probe(self, scope_changed, chosen):





        if not all((SRC / p).exists() for p in scope_changed):
            return None
        w, _ = self.broken_module_tests(sorted(scope_changed))
        w |= self._lazy_probe_extra(scope_changed)
        if not self._free(chosen, w):
            return None
        if len(w) < len(self.all):
            srv = _probe_server()
            asked = srv.asked_names()
            if asked is None:
                return None
            names = set()
            for rel in scope_changed:
                name = rel[:-3].replace("/", ".")
                names.add(name[: -len(".__init__")] if name.endswith(".__init__") else name)
            if names & asked:
                return None
        return w

    def _lazy_probe_extra(self, scope_changed):







        try:
            base = _baseline_full()
            tm = set(test_modules())
        except Exception:
            return set(self.all)
        files = set()
        for p in scope_changed:
            files |= self.import_closure(p)
        out = set()
        for f in files:
            out |= self.func_import_users(f) | self.by_file.get(f, set())
        for f, nums in self.by_file.items():
            if f not in tm or _mod_name(f) in base:
                out |= nums
        return out

    def pack(self, chosen):
        if not chosen:
            return []
        return self.fill(lpt_pack(self.ms, chosen), chosen)

    def fill(self, bins, chosen):



        loads = [sum(self.ms[n] for n in b) for b in bins]
        cap = max(loads)
        used = set(chosen)
        for tier in self.insurance:
            for n in sorted(tier - used, key=lambda n: (self.ms[n], n)):
                j = min(range(len(bins)), key=lambda i: (loads[i], i))
                if loads[j] + self.ms[n] <= cap:
                    bins[j].append(n)
                    loads[j] += self.ms[n]
                    used.add(n)
        return bins


_TRACE_HEAD = r"""
import sys as _s, os as _o, json as _j, atexit as _ae
_started = set()
_M = _s.monitoring
_M.use_tool_id(3, "rwx-import-trace")
def _cb(code, off):
    _started.add((code.co_filename, code.co_qualname))
    return _M.DISABLE
_M.register_callback(3, _M.events.PY_START, _cb)
_M.set_events(3, _M.events.PY_START)
def _dump():
    _M.set_events(3, 0)
    with open(_o.environ["RWX_TRACE_OUT"], "w", encoding="utf-8") as _fh:
        _j.dump(sorted(_started), _fh)
_ae.register(_dump)
"""


def import_trace():





    import subprocess
    import tempfile
    from concurrent.futures import ThreadPoolExecutor
    mods = _all_modules()
    pre = str(SRC).replace("\\", "/").rstrip("/") + "/"

    def one(extra):
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8") as fh:
            json.dump({"patched": {}, "extra": extra}, fh)
            cfg = fh.name
        out = cfg + ".trace"
        try:
            subprocess.run([sys.executable, "-I", "-S", "-c", _TRACE_HEAD + _IMPORT_PROBE, cfg, str(SRC)],
                           capture_output=True, timeout=300, env={**os.environ, "RWX_TRACE_OUT": out})
            with open(out, encoding="utf-8") as fh:
                return json.load(fh)
        finally:
            for f in (cfg, out):
                try:
                    os.unlink(f)
                except OSError:
                    pass

    started = {}
    with ThreadPoolExecutor(4) as ex:
        for res in ex.map(one, [mods] + [[m] for m in mods]):
            for fn, qn in res:
                fn = fn.replace("\\", "/")
                if fn.startswith(pre):
                    started.setdefault(fn[len(pre):], set()).add(qn)
    CACHE.mkdir(parents=True, exist_ok=True)
    (CACHE / "import_started.json").write_text(json.dumps({f: sorted(v) for f, v in started.items()}), encoding="utf-8")
    log(f"import trace: {len(mods)} modules, {sum(map(len, started.values()))} code objects started at import")


class _Verifier:

    def __init__(self, sel, tests):
        self.sel = sel
        self.id = {t["number"]: t["id"] for t in tests}
        self.never = {n for n, i in self.id.items() if i.rsplit("::", 1)[-1] in VERIFY_NEVER}
        try:
            vc = json.loads((APP / "cache" / "vcost.json").read_text(encoding="utf-8"))
        except (OSError, ValueError):
            vc = {}
        self.cost_ms = {n: vc.get(i, 2 * sel.ms[n] + VERIFY_TEST_MS) for n, i in self.id.items()}
        self.wall_s = 0.0
        self.proc = None
        self.dead = False
        self.spent_ms = 0
        self.n = 0

    def _cost(self, bins):
        bins = [b for b in bins if b]
        return max(sum(self.sel.ms[n] for n in b) for b in bins) + WORKER_COST_MS * len(bins) if bins else 0

    def _start(self):
        import subprocess
        self.spent_ms += VERIFY_BOOT_MS
        self.proc = subprocess.Popen([sys.executable, "-S", str(APP / "vserve.py")], stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        line = self.proc.stdout.readline()
        r = json.loads(line) if line else {}
        if not r.get("ready"):
            raise RuntimeError("verify server did not start")
        self.spent_ms += r["cpu_ms"] - VERIFY_BOOT_MS

    def check(self, text, workers):

        if self.dead or not workers:
            return workers, None
        printed = [n for b in workers for n in b]
        keep = sorted(n for n in printed if n in self.never)
        cand = [n for n in printed if n not in self.never]
        if not cand:
            return workers, None
        kept = lpt_pack(self.sel.ms, set(keep)) if keep else []
        saving = self._cost(workers) - self._cost(kept)
        tests_ms = sum(self.cost_ms[n] for n in cand)
        exp_cpu = VERIFY_START_MS + VERIFY_P0 * tests_ms + (1 - VERIFY_P0) * tests_ms / 2
        if saving * VERIFY_P0 <= exp_cpu:
            return workers, None
        boot = 0 if self.proc else VERIFY_BOOT_MS
        if self.spent_ms + boot + VERIFY_START_MS + tests_ms > VERIFY_BUDGET_MS:
            return workers, f"verify skipped: budget ({self.spent_ms} ms spent)"

        by_cls = {}
        for n in cand:
            by_cls.setdefault(self.id[n].rsplit("::", 1)[0], []).append(n)
        groups = sorted((sorted(v, key=lambda n: (self.cost_ms[n], n)) for v in by_cls.values()),
                        key=lambda g: (self.cost_ms[g[0]], g[0]))
        order = [self.id[n] for g in groups for n in g]
        cap_s = max(1, math.ceil((3 * tests_ms + 500) / 1000))
        w0 = time.monotonic()
        try:
            if self.proc is None:
                self._start()
            self.proc.stdin.write((json.dumps({"patch": text, "tests": order, "cpu_s": cap_s,
                                                "max_start_ms": round(saving * VERIFY_P0 - exp_cpu + VERIFY_START_MS)}) + chr(10)).encode())
            self.proc.stdin.flush()
            r = json.loads(self.proc.stdout.readline())
        except Exception as e:
            self.dead = True
            return workers, f"verify error {type(e).__name__}"
        finally:
            self.wall_s += time.monotonic() - w0
        self.n += 1
        self.spent_ms += r["cpu_ms"]
        why = f"verify {len(cand)} tests: {r['verdict']} {r['why']} ({r['cpu_ms']} ms)"
        if r["verdict"] == "pass":
            return kept, why
        return workers, why

    def close(self):
        if self.proc is not None:
            try:
                self.proc.stdin.close()
                self.proc.wait(timeout=10)
            except Exception:
                self.proc.kill()
                self.proc.wait()


def precompute():
    import hashlib
    import marshal
    try:
        build_compact_map(MAP, CACHE / "map.bin")
    except Exception as e:
        log(f"compact map not built ({type(e).__name__}: {e}): the gzip JSON map will be used")
    for p in (APP / "e1map.json.gz", E2_MAP, R1_MAP):
        try:
            build_map_pickle(p)
        except Exception as e:
            log(f"map pickle for {p.name} not built ({type(e).__name__}: {e})")
    n = 0
    for p in sorted(SRC.rglob("*.py")):
        rel = p.relative_to(SRC).as_posix()
        try:
            text = p.read_text(encoding="utf-8")
            co = compile(_src_bytes(text), rel, "exec", dont_inherit=True)
        except Exception:
            continue
        f = _cache_file("code", rel)
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_bytes(hashlib.sha1(text.encode("utf-8", "surrogatepass")).hexdigest().encode() + marshal.dumps(co))
        n += 1
    idx = {}
    for p in sorted(SRC.rglob("*.py")):
        rel = p.relative_to(SRC).as_posix()
        try:
            text = p.read_text(encoding="utf-8")
            idx[rel] = [hashlib.sha1(text.encode("utf-8", "surrogatepass")).hexdigest(), sorted(import_scope_names(text))]
        except Exception:
            continue
    CACHE.mkdir(parents=True, exist_ok=True)
    import pickle
    nr = {}
    for p in sorted([*(SRC / "sqlglot").rglob("*.py"), *(SRC / "tests").rglob("*.py")]):
        try:
            text = p.read_text(encoding="utf-8")
            nr[hashlib.sha1(text.encode("utf-8", "surrogatepass")).hexdigest()] = _name_reads_index(text)
        except Exception:
            continue
    with open(CACHE / "name_reads.pickle", "wb") as fh:
        pickle.dump(nr, fh, protocol=pickle.HIGHEST_PROTOCOL)
    (CACHE / "import_names.json").write_text(json.dumps(idx), encoding="utf-8")
    (CACHE / "func_imports.json").write_text(json.dumps(_func_import_index()), encoding="utf-8")
    (CACHE / "name_refs.json").write_text(json.dumps(_ref_index()), encoding="utf-8")
    log(f"precompute: compact map, {n} compiled pinned files, {len(idx)} import-scope name sets")








GC_VALVE_MB = 1500


def _maxrss_mb():
    try:
        import resource
        return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024
    except Exception:
        return float("inf")


def main():
    if sys.argv[1:] == ["--baseline"]:
        base = sorted(_probe_all())
        (APP / "import_baseline.json").write_text(json.dumps(base), encoding="utf-8")
        log(f"import baseline: {len(base)} modules fail without any patch: {base}")
        full = sorted(_baseline_full())
        (APP / "import_baseline_full.json").write_text(json.dumps(full), encoding="utf-8")
        log(f"collection-probe baseline: {len(full)} modules fail without any patch: {full}")
        _close_probe_server()
        return
    if sys.argv[1:] == ["--precompute"]:
        precompute()
        import_trace()
        return
    t0 = time.monotonic()
    prof = None
    if os.environ.get("RWX_PROF") == "1":
        import prof
        g = globals()
        log(f"PROF startup-to-main {prof.cpu_now():.3f}s")
        for fn in ("import_fails", "parse_patch", "code_changes", "e2_expected", "top_level_changes"):
            g[fn] = prof.wrap(fn, g[fn])
        for m in ("__init__", "collection_broken", "e2_readers", "_ns_diff", "e1_check", "e1s_check",
                  "_lazy_probe", "loader_invisible", "name_readers"):
            setattr(Selector, m, prof.wrap("Selector." + m, getattr(Selector, m)))



    gc.disable()
    tests = json.loads((DATA / "tests.json").read_text(encoding="utf-8"))["tests"]
    patches = sorted((DATA / "commits").glob("*.patch"))
    out_lock, done = threading.Lock(), set()

    def watchdog():


        with out_lock:
            ms = {t["number"]: math.floor(t["seconds"] * 1000 + 0.5) for t in tests}
            everything = lpt_pack(ms, set(ms))
            left = [p for p in patches if p.stem not in done]
            for p in left:
                sys.stdout.write(json.dumps({"commit": p.stem, "workers": everything}) + "\n")
            sys.stdout.flush()
            log(f"WATCHDOG at {time.monotonic() - t0:.1f}s: {len(left)} commits answered with all tests")
            t = os.times()
            log(f"CPU self user+sys {t.user + t.system:.3f}s children {t.children_user + t.children_system:.3f}s")
            sys.stderr.flush()
            os._exit(0)
    timer = threading.Timer(max(0.0, WATCHDOG_FRACTION * RUN_LIMIT_S - (time.monotonic() - t0)), watchdog)
    timer.daemon = True
    timer.start()
    sel = Selector(MAP, tests)
    ver = _Verifier(sel, tests)
    for i, patch in enumerate(patches):
        raw = patch.read_bytes()
        text = patch.read_text(encoding="utf-8", errors="replace")




        spent = time.monotonic() - t0
        projected = spent + (spent / i) * (len(patches) - i) if i >= max(1, len(patches) // 4) else spent
        allow_probe = spent < SAFE_FRACTION * RUN_LIMIT_S and projected < 0.9 * WATCHDOG_FRACTION * RUN_LIMIT_S
        try:
            chosen, why = sel.select(text, allow_probe=allow_probe, raw=raw)
        except Exception as e:
            chosen, why = set(sel.all), [f"selector error {type(e).__name__}: {e}"]
        workers = sel.pack(chosen)
        if VERIFY and not sel.order_hit:
            workers, vwhy = ver.check(text, workers)
            if vwhy:
                why = list(why) + [vwhy]
        with out_lock:
            sys.stdout.write(json.dumps({"commit": patch.stem, "workers": workers}) + "\n")
            sys.stdout.flush()
            done.add(patch.stem)
        log(f"{patch.stem}: {len(chosen)} tests, {len(workers)} workers | " + "; ".join(why))
        if prof is not None and prof.CALLS:
            log(f"PROFC {patch.stem} " + " ".join(f"{n}={c:.2f}" for n, c in prof.CALLS if c >= 0.05))
            prof.CALLS.clear()
        if os.environ.get("RWX_LOG_CHOSEN"):
            log(f"CHOSEN {patch.stem} {json.dumps(sorted(chosen))}")
        if not gc.isenabled() and _maxrss_mb() > GC_VALVE_MB:
            gc.enable()
            gc.collect()
    timer.cancel()
    sys.stdout.flush()
    ver.close()
    if ver.n:
        log(f"verify: {ver.n} commits, {ver.spent_ms} ms CPU")
    _close_probe_server()
    t = os.times()
    log(f"CPU self user+sys {t.user + t.system:.3f}s children {t.children_user + t.children_system:.3f}s")
    if prof is not None:
        prof.report(log, t.user + t.system + t.children_user + t.children_system)


if __name__ == "__main__":
    main()
