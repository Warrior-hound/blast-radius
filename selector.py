"""Blast Radius selector: for each patch, choose the tests that can catch it and pack them on workers.

Pipeline per commit (each stage only handles what the earlier, cheaper ones could not settle):
  1. Parse the unified diff and rebuild each changed file's new text in memory.
  2. Null-perturbation check (.py): compile old and new; code objects identical apart from line
     numbers => the change cannot alter behavior => contributes no tests.
  3. Exposure (.py): for each code object whose own code changed, the tests that executed any line
     of it at the pinned commit (per-test trace map). Added/removed code charges its enclosing scope.
     An edit inside a function body is narrowed to the statements it touches (statement_ranges);
     class bodies are compared without their __firstlineno__ line-number constant.
  4. Non-code files: tests that opened the file during the traced run (fixtures).
  5. Anything the map cannot reason about (syntax errors in imported modules, test configuration,
     unparseable patches) falls back to a wider, safe set.
  6. Pack the chosen tests on k <= 8 workers (LPT), choosing k to minimise max load + 2 s * k.
Logs go to stderr; stdout carries exactly one JSON line per commit.
"""
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
# Rule switches, for measuring each rule's effect on labeled sets (defaults are what ships).
IMPORT_TIME_RULE = os.environ.get("RWX_IMPORT_TIME_RULE", "0") == "1"  # off: costs ~43 s on the sample, caught 0 misses so far
# frame-changing edits narrowed to the statements whose instructions differ (DejaVu), and functions
# that ran at collection narrowed when no divergent statement ran there
FRAME_DIFF = os.environ.get("RWX_FRAME_DIFF", "1") == "1"
E1 = os.environ.get("RWX_E1", "1") == "1"  # on by default; stage-boundary early cutoff for the TPC executor tests (e1_cutoff.py)
WORKER_COST_MS = 2000
PROBE_TIMEOUT_S = 10  # measured probes take <= 0.6 s
# The run's time limit for the whole batch (spec: 3 min practice, 4.5 min final with ~1.5x commits).
# Use the smaller one; once a safe fraction of it is spent, skip import probes and widen instead.
RUN_LIMIT_S = float(os.environ.get("RWX_RUN_LIMIT_S", "180"))
SAFE_FRACTION = 0.5  # import probes stop here
E1_BUDGET_S = 0.15 * RUN_LIMIT_S  # E1 checks stop (keeping their tests) once they have used this much
WATCHDOG_FRACTION = 0.7  # every unanswered commit gets the whole suite here

CONFIG_FILES = {"conftest.py", "tests/conftest.py", "setup.cfg", "pytest.ini", "tox.ini", "pyproject.toml"}


# E2: class-body / module-level value edits select only the tests that READ a changed attribute,
# global or table key (read map traced at the pinned commit + namespace diff of a patched import).
E2 = os.environ.get("RWX_E2", "0") == "1"
# E2_PRUNE off (guard g8, add-only): the diff runs only when a module's bindings change and only ADDS
# the readers of the registries it changed; v7's selection is kept whole. On: readers also replace
# class_users / name_readers for class-body and module-level value edits.
E2_PRUNE = os.environ.get("RWX_E2_PRUNE", "0") == "1"
E2_MAP = Path(os.environ.get("RWX_E2_MAP", APP / "e2map.json.gz"))
E2_TIMEOUT_S = 20
E2_COST_MS = 1600  # measured CPU of one namespace diff (interpreter, import, fingerprint)
E2_FP = Path(os.environ.get("RWX_E2_FP", APP / "cache" / "e2fp.pickle"))  # written at image build
E2_CANON = E2_FP.with_suffix(".canon.json")


# Parsed trees of the last few texts: one commit parses the same old/new text in several stages
# (e2_expected, _FileInfo, top_level_changes, operator_swaps_in) and importers again across commits.
# Every consumer only reads the tree (the two that blank a field restore it in try/finally), so a
# shared tree gives the same results. Failures are not cached: they raise again, the same way.
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


def _scope_bindings(body):
    """{name: [statement dumps]} for the bindings a module or class body makes directly (assignments,
    imports, docstring), plus the dumps of its other non-def statements (key None)."""
    out = {}

    def add(k, v):
        out.setdefault(k, []).append(v)

    def walk(stmts, first):
        for i, st in enumerate(stmts):
            if first and i == 0 and isinstance(st, ast.Expr) and isinstance(st.value, ast.Constant)                     and isinstance(st.value.value, str):
                add("__doc__", ast.dump(st))
            elif isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                add(("def", st.name), "def")  # bodies: code regions / class bodies below
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


def e2_expected(path, old_text, new_text):
    """What a namespace diff of this edit must show: (exact locations, location prefixes). Every
    binding the edit changes at module or class scope must appear as a changed location; other
    changed module / class statements need some change in that scope. None: cannot tell."""
    try:
        to, tn = _parse(old_text), _parse(new_text)
    except (SyntaxError, ValueError):
        return None
    mod = path[:-3].replace("/", ".")
    if mod.endswith(".__init__"):
        mod = mod[: -len(".__init__")]
    exact, prefixes = set(), set()

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

    def compare(bo, bn, loc_of, prefix):
        a, b = _scope_bindings(bo), _scope_bindings(bn)
        for k in set(a) | set(b):
            if a.get(k) == b.get(k):
                continue
            if k is None:
                prefixes.add(prefix)
            elif isinstance(k, tuple):  # a def / class added or removed
                exact.add(loc_of(k[1]))
            else:
                exact.add(loc_of(k))
    compare(to.body, tn.body, lambda n: f"G|{mod}|{n}", f"G|{mod}|")
    co, cn = classes(to), classes(tn)
    for q in set(co) & set(cn):
        compare(co[q].body, cn[q].body, lambda n, q=q: f"C|{mod}:{q}|{n}", f"C|{mod}:{q}|")
    return exact, prefixes


def _mod_file(mod):
    """Pinned-tree path of module `mod`, or None."""
    for rel in (mod.replace(".", "/") + ".py", mod.replace(".", "/") + "/__init__.py"):
        if (SRC / rel).exists():
            return rel
    return None


def log(*a):
    print(*a, file=sys.stderr)


# ---------------------------------------------------------------- patch parsing

HUNK = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


def parse_patch(text):
    """Return list of file diffs: {old, new, hunks:[(old_start, old_len, new_start, new_len, lines)]}."""
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
                        break  # the @@ counts are complete: what follows is not this hunk's
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
    """Rebuild the new text; returns (new_text, changed_old_lines, insertion_points) or raises."""
    old = old_text.split("\n")
    out, pos = [], 0  # pos: 0-based index into old
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
                inserts.add(pos + 1)  # inserted before old line pos+1
        _ = no_newline
    out.extend(old[pos:])
    return "\n".join(out), changed, inserts


# ---------------------------------------------------------------- code object diff

def _canon(c):
    """Order-independent, value-based form of a constant (frozenset iteration order varies between
    compiles of the same source, so repr() would report false changes)."""
    if isinstance(c, types.CodeType):
        return ("<code>", c.co_name)
    if isinstance(c, frozenset):
        return ("frozenset", tuple(sorted((_canon(e) for e in c), key=repr)))
    if isinstance(c, tuple):
        return ("tuple", tuple(_canon(e) for e in c))
    return (type(c).__name__, repr(c))


def _line_number_consts(co):
    """Indexes of constants that only record a line number: Python 3.13 class bodies store
    `__firstlineno__ = <line>`, so moving a class (any line added above it) changes that constant
    without changing behavior. Normalized only when that constant is loaded nowhere else."""
    if "__firstlineno__" not in co.co_names:
        return ()
    # The candidate constant indexes depend only on the instruction stream (co_code) and the
    # STORE_NAME targets (co_names), so they are memoized on those; the int check is per object.
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
    """Same result as _own_signature(oco) != _own_signature(nco), checking the cheap fields first."""
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
    """Map a stable path key -> code object. Siblings with the same name get an occurrence index."""
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


# ---------------------------------------------------------------- statement-level regions
#
# Soundness argument: a test whose behavior changes first diverges from the old run when it is
# about to execute changed code. If that is a removed/edited statement, the test executed that
# statement in the old run (some line of its own range). If it is an inserted statement, the
# test reached its position, so in the old run it executed the statement just before it in the same
# block (or the block's header). So the tests that executed those old statements cover every test
# that can change, as long as the rest of the function means the same thing (same locals, cells,
# free variables, names, flags, signature). Anything else falls back to the whole function.

_SIMPLE_HEADER = (ast.If, ast.For, ast.AsyncFor, ast.While, ast.With, ast.AsyncWith)
_DEFS = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
_GAPPY = (ast.Try, ast.Match) + ((ast.TryStar,) if hasattr(ast, "TryStar") else ())


def _first_line(node):
    return min([node.lineno] + [d.lineno for d in getattr(node, "decorator_list", ())])


def _own_range(node):
    """Lines that every execution of the statement runs part of (used for the selection)."""
    if isinstance(node, _SIMPLE_HEADER + _DEFS):
        return _first_line(node), max(_first_line(node), node.body[0].lineno - 1)
    return _first_line(node), node.end_lineno  # simple statements; try/match: the whole statement


def _header_range(node):
    """Lines that belong to the statement itself rather than to a nested statement."""
    if isinstance(node, _GAPPY):
        return None  # gaps (try:/except:/else:/finally:/case) are not localizable
    return _own_range(node)


class _FileInfo:
    def __init__(self, text):
        self.lines = text.split("\n")
        self.tree = _parse(text)
        self.funcs = {}
        self.strings = set()  # lines inside multi-line string literals
        # Same nodes as ast.walk would yield for what is collected here: a node that fits on one
        # line can contain neither a def (a def is a statement; a one-line statement holds no other
        # def) nor a multi-line literal (children lie inside their parent's lines), so its subtree
        # is skipped. funcs lists are only ever tested for a single match, so order is irrelevant.
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
    """(statement, parent, block, index) for the statements owned by function fn (not by nested
    defs/classes, whose bodies have their own code objects)."""
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
    """The deepest statement whose lines contain ln."""
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
    """removed old lines, inserted new lines, and the new->old map of kept lines."""
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
    # co_names (globals and attributes looked up) is compared too: a statement-level edit that starts
    # using a new name can change state that outlives the test (e.g. a hand-rolled per-class cache
    # filled once per process), so tests that never ran the edited statement would still observe it.
    # Locals, cells and free variables: an assignment can turn a name local (or a cell) for the whole function.
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


def _class_attrs(fi):
    """Names bound directly in some class body of the file (class-level attributes)."""
    out = getattr(fi, "_class_attrs", None)
    if out is None:
        out = set()
        for c in ast.walk(fi.tree):
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
    """True when the function body (not nested defs or lambdas) writes into state that outlives the
    call: a `global`/`nonlocal` statement; a subscript/attribute store or delete, or a mutating method
    call (`append`, `update`, `setdefault`, ...), on an object reached from a module-level name, the
    class argument, a call result (`globals()[k]`, `type(self).x`), `<x>.__class__`, or a class-level
    attribute through the first parameter (`self.REGISTRY[k] = v`); or a setattr/delattr call. Such a
    write can carry an edited statement's effect to tests that never execute that statement."""
    local = set(co.co_varnames) | set(co.co_cellvars) | set(co.co_freevars)
    params = fn.args.posonlyargs + fn.args.args
    first = params[0].arg if params else None
    cls_arg = first if first in _CLS_LIKE else None
    cattrs = _class_attrs(fi) if fi is not None else None

    def shared(obj):
        # obj is the object written into; True when it can outlive the call
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


# ---------------------------------------------------------------- frame-changing edits (DejaVu)
#
# An edit that changes the frame (a name becomes local or global, a name is no longer looked up)
# can change the meaning of statements whose text did not change. Rothermel & Harrold's safe RTS:
# execution is identical to the old run until the first instruction whose semantics differ, so the
# tests that can change are those that executed a statement whose compiled instructions differ.
# Each kept line's instructions are compared with names resolved (LOAD_FAST x vs LOAD_GLOBAL x
# differ; local slot and name-table indexes do not matter), constants by value, and control flow by
# where it goes: jump targets, fall-through successors and exception handlers are compared as the
# (old line, index) of the instruction they reach. Anything not attributable to a line, or a frame
# difference outside locals and looked-up names, falls back to the whole function.

_NO_FALLTHROUGH = {"RETURN_VALUE", "RETURN_CONST", "RAISE_VARARGS", "RERAISE", "JUMP_FORWARD", "JUMP_BACKWARD",
                   "JUMP_BACKWARD_NO_INTERRUPT", "JUMP"}
_SKIP_OPS = {"NOP", "EXTENDED_ARG", "CACHE"}
# names that expose the frame itself: the set of locals is then observable
_FRAME_NAMES = {"locals", "vars", "exec", "eval", "_getframe", "currentframe", "f_locals", "f_back", "dir", "globals"}


def _relaxable_frame(oco, nco):
    """Frame differences the per-line comparison can account for: only the locals and the names
    looked up. Signature, parameter names, cells, free variables and flags must be the same."""
    if not (oco.co_flags == nco.co_flags and oco.co_argcount == nco.co_argcount
            and oco.co_posonlyargcount == nco.co_posonlyargcount and oco.co_kwonlyargcount == nco.co_kwonlyargcount
            and oco.co_cellvars == nco.co_cellvars and oco.co_freevars == nco.co_freevars):
        return False
    n = oco.co_argcount + oco.co_kwonlyargcount + bool(oco.co_flags & 0x04) + bool(oco.co_flags & 0x08)
    if oco.co_varnames[:n] != nco.co_varnames[:n]:
        return False
    return not (_FRAME_NAMES & (set(oco.co_names) | set(nco.co_names)))


def _instructions(co, line_key):
    """({identity: normalized instruction}, {identity: predecessor identities}) for co's own
    instructions. An identity is (line key, index among that line's instructions); line_key maps a
    source line (or None) to the key that identifies it across old and new."""
    import dis
    every = list(dis.get_instructions(co))
    ins = [i for i in every if i.opname not in _SKIP_OPS]
    ident, count = {}, {}
    for i in ins:
        k = line_key(i.positions.lineno if i.positions else None)
        n = count.get(k, 0)
        count[k] = n + 1
        ident[i.offset] = (k, n)
    resolved, nxt = {}, ("<end>",)  # an offset on a skipped instruction reaches the next kept one
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
            arg = i.argrepr  # the resolved name, plus flags such as "NULL|self +"
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
    """Old lines whose instructions differ from the new code's, by instruction identity. The first
    instruction a test executes differently is one the old code has (the instruction executed
    before it is the same in both, so it reaches the same identity), so only old identities count.
    An instruction without a line number is charged to the lines that can reach it in the old code.
    Lines the edit removed are included (the textual diff targets them too)."""
    old, opred = _instructions(oco, lambda ln: ln)
    new, _ = _instructions(nco, lambda ln: ln if ln is None else new2old.get(ln, ("new", ln)))
    out, todo, seen = set(), [], set()
    for k, v in old.items():
        w = new.get(k)
        if w == v:
            continue
        if w is None or w[:2] != v[:2] or (v[3] is None) != (w[3] is None) or (v[3] and v[3][1:] != w[3][1:]):
            todo.append(k)  # the instruction itself does something else
            continue
        # same operation, different destination: a test diverges only when it goes there, and in
        # the old run it then executed the old destination (or, without a line, this instruction)
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
                return None  # unreachable from any line: cannot attribute it
            todo.extend(opred[k])
        elif isinstance(k[0], int):
            out.add(k[0])
    return out


def statement_ranges(oco, nco, old_fi, new_fi, diff):
    """Old-file line ranges whose executing tests cover every test the edit to this function can
    affect, or None when the edit cannot be localized (the caller then uses the whole function)."""
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
        by_first.setdefault(_first_line(e[0]), e[0])  # outermost statement starting on that line
    olines = _code_lines(oco)
    targets = []

    def doc(fn, s):
        b = fn.body[0]
        return (s is b and isinstance(b, ast.Expr) and isinstance(b.value, ast.Constant)
                and isinstance(b.value.value, str))

    def target_old(s):
        r = _own_range(s)
        if not any(r[0] <= ln <= r[1] for ln in olines):
            return False  # no bytecode there: its executions are not observable in the map
        targets.append(r)
        return True

    def old_twin(node):
        o = new2old.get(_first_line(node))
        t = by_first.get(o) if o is not None else None
        return t if t is not None and type(t) is type(node) else None

    def position(entry, depth=0):
        """Old statements that every test reaching this new statement's position executed."""
        s, parent, blk, i = entry
        if depth > 200:
            return False
        # Same block in the old function with the same number of statements: a test that first
        # diverges here reached position i of that block in the old run too, so it began old
        # statement i there.
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
            return False  # first statement of the function, or of a try/except/case block
        t = old_twin(parent)
        if t is not None:
            return target_old(t)
        return position(next(x for x in nst if x[0] is parent), depth + 1)

    for ln in sorted(removed):
        if not _first_line(ofn) <= ln <= ofn.end_lineno or old_fi.ignorable(ln):
            continue
        e = _innermost(ost, ln)
        if e is None or doc(ofn, e[0]):
            return None  # signature, decorators or docstring
        s = e[0]
        if _in_nested_body(s, ln):
            continue  # belongs to the nested code object, which is compared on its own
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
        t = old_twin(s)  # an edited statement: the tests that ran its old version
        if not (target_old(t) if t is not None else position(e)):
            return None
    if FRAME_DIFF:
        # the frame changed: kept statements whose instructions now mean something else
        div = _divergent_lines(oco, nco, new2old)
        if div is None:
            return None
        for ln in sorted(div):
            e = _innermost(ost, ln)
            if e is None or doc(ofn, e[0]):
                return None
            s = e[0]
            if _in_nested_body(s, ln):
                return None  # the parent's instructions never sit in a nested body
            h = _header_range(s)
            if h is None or not h[0] <= ln <= h[1] or not target_old(s):
                return None
    return targets or None


_compiled = {}


def _src_bytes(text):
    """Source as the import system sees it: bytes, so a PEP 263 encoding cookie on line 1-2 is
    honoured (compiling a str ignores the cookie: a cookie edit would look bytecode-identical while
    the real import fails or decodes the literals differently)."""
    return text.encode("utf-8", "surrogatepass")


CACHE = APP / "cache"  # written at image build (`selector.py --precompute`); every use is checked


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
    """The pinned file's code object, compiled at image build. Used only when the cached source
    digest matches this exact text (otherwise None: compile it here)."""
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
    """Return ('null', []) | ('syntax', []) | ('changed', [(kind, [(lo, hi), ...], qualname, whole)...]).
    kind is 'func' for a function-like code object, 'scope' for a module or class body; whole is the
    code object's full span. With the hunks, an edited function is narrowed to the statements the
    edit touches (statement_ranges)."""
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
        # own: the lines its body runs (the first line also carries the enclosing scope's def
        # statement; a one-line lambda keeps it)
        own = (_code_lines(co) - {co.co_firstlineno}) or _code_lines(co)
        regions.append((kind(co), ranges or [_span(co)], co.co_qualname, _span(co), own))

    def scope_of(key):
        # parent key of a code object
        return key.rsplit("/", 1)[0] if "/" in key else ""

    def kind(co):
        return "func" if co.co_flags & 0x0002 else "scope"  # CO_NEWLOCALS: functions, lambdas, comprehensions

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
            # added code: charge the nearest existing ancestor scope
            k = scope_of(key)
            while k not in old_map and k:
                k = scope_of(k)
            parent = old_map.get(k, old_co)
            add(parent)
    if not regions:
        return "null", []
    return "changed", regions


# ---------------------------------------------------------------- module-level names (static)

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
    return False  # attribute / subscript store: mutates another object


def _sig(node):
    """ast.dump of a statement with a function's body left out (the body is its own code object,
    compared on its own): what binding the name means to a reader of the module."""
    if isinstance(node, _DEF):
        body, node.body = node.body, []
        try:
            return ast.dump(node)
        finally:
            node.body = body
    return ast.dump(node)


def _top_level(tree):
    """{name: [signatures of the top-level statements binding it]}, [signatures of top-level
    statements with effects beyond binding names (calls, attribute/subscript stores, ...)]."""
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
                continue  # class bodies: their users come from the map's class users
            elif isinstance(n, _DEF):
                bound.add(n.name)
            elif isinstance(n, ast.Assign):
                pure = all([_bound(t, bound) for t in n.targets])
            elif isinstance(n, (ast.AnnAssign, ast.AugAssign)):
                pure = _bound(n.target, bound)
            elif isinstance(n, ast.Expr) and isinstance(n.value, ast.Constant):
                continue  # docstring / bare literal
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
    """(names whose top-level binding changed or disappeared, names added, effects changed?)."""
    on, oe = _top_level(_parse(old_text))
    nn, ne = _top_level(_parse(new_text))
    changed = {k for k, v in on.items() if sorted(v) != sorted(nn.get(k, []))}
    added = set(nn) - set(on)
    return changed, added, sorted(oe) != sorted(ne)


def name_reads(text, names):
    """Line ranges inside function bodies where the module loads one of `names` (directly, via an
    `as` alias of `from ... import NAME`, or as an attribute `mod.NAME`); None when any load happens
    at import scope (module level, class bodies, decorators, defaults)."""
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
                continue  # binding the name is not reading it
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
    """Names loaded while the module is imported: module level and class bodies (with decorators,
    default values, bases), plus, transitively, the bodies of the module's own top-level functions
    that import-time code refers to (a factory called from a class body runs at import)."""
    tree = _parse(text)
    funcs = {n.name: n for n in tree.body if isinstance(n, _DEF)}
    out = set()

    def loads(root, into, enter):
        todo = list(root.body) if enter else [root]
        while todo:
            n = todo.pop()
            if isinstance(n, _DEF):  # def statement: decorators and defaults run, the body does not
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


# ---------------------------------------------------------------- import check

# The probes import sqlglot the way the test run does: `unittest` is loaded first (every test
# module imports it, and pytest's runner is in sys.modules too), because sqlglot reads that at import
# time (expressions/core.py UNITTEST turns on strict argument checks that also run while dialect
# modules build expressions at import). A probe without it can pass while the tests' imports fail.
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
failed = []
try:
    import sqlglot
except BaseException as e:
    failed.append("sqlglot")
for name in list(patched) + _cfg["extra"]:
    try:
        importlib.import_module(name)
    except BaseException as e:
        failed.append(name)
print(json.dumps(failed))
"""


_BASELINE = None


def _baseline_failures():
    """Modules that fail to import from the pinned tree with no patch at all. Written at image build
    time (`selector.py --baseline`); computed on first use when absent."""
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
    """Modules the import probe can load: the package and the test suite's shared helper modules
    (tests/helpers.py and the like are imported by many test files at collection; a module-level
    error there fails all of them). Test files themselves are covered by their own tests."""
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


# Warm probe parent. A cold probe is a fresh `python -I -S` that runs _IMPORT_PROBE: it imports
# sqlglot with the patched modules served from memory, then each patched module and importer. The
# warm parent is that same interpreter (same flags, sys.path, meta_path finder, argv shape) stopped
# right after its unpatched `import sqlglot`; it records every module name the import system was
# asked for during that import. For a probe whose patched modules include none of those names, a
# fresh probe's `import sqlglot` runs exactly the same code, so a fork of the parent is in the state
# the fresh probe reaches there; the child then installs the patched sources, runs the rest of
# _IMPORT_PROBE unchanged and exits through normal interpreter shutdown (threads joined, atexit
# run). Probes that patch a module that `import sqlglot` itself asks for run cold, as before.
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
while _ok:
    _line = _inp.readline()
    if not _line:
        break
    _req = json.loads(_line)
    sys.stdout.flush()
    sys.stderr.flush()
    _pid = os.fork()
    if _pid == 0:
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
        for name in list(patched) + _cfg["extra"]:
            try:
                importlib.import_module(name)
            except BaseException as e:
                failed.append(name)
        print(json.dumps(failed))
        sys.exit(0)
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
        fd, self.err0 = tempfile.mkstemp(suffix=".err")  # the parent's own stderr: import-time output
        os.close(fd)
        with open(self.err0, "wb") as err:
            self.proc = subprocess.Popen([sys.executable, "-I", "-S", "-c", _PROBE_SERVER, str(SRC)],
                                         stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=err)
        hello = self._line(PROBE_TIMEOUT_S * 3)
        if not hello or not hello.get("ok"):
            raise RuntimeError("probe server unavailable")
        self.asked = set(hello["asked"])
        with open(self.err0, "rb") as fh:
            self.prefix = fh.read()  # what a cold probe prints to stderr during `import sqlglot`

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

    def run(self, cfg, names):
        """CompletedProcess-like result of the probe, or None when it must run cold."""
        import io
        import subprocess
        import tempfile
        if self.dead or not hasattr(os, "fork"):
            return None
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


_SERVER = None


def _probe_server():
    global _SERVER
    if _SERVER is None:
        _SERVER = _ProbeServer()
    return _SERVER


def _close_probe_server():
    if _SERVER is not None:
        _SERVER.close()


def import_fails(src_root, patched_files, also_import=()):
    """Import the patched modules (plus sqlglot itself) in a throwaway interpreter.
    patched_files: {relative path: new source}. True when the import raises."""
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
        json.dump({"patched": mods, "extra": extra}, fh)
        tmp = fh.name
    try:
        r = None
        if str(src_root) == str(SRC):
            r = _probe_server().run(tmp, set(mods))  # None: not eligible, run it the cold way
        if r is None:
            r = subprocess.run([sys.executable, "-I", "-S", "-c", _IMPORT_PROBE, tmp, str(src_root)],
                               capture_output=True, text=True, timeout=PROBE_TIMEOUT_S)
        try:
            failed = set(json.loads(r.stdout.strip().splitlines()[-1]))
        except Exception:
            return True, "probe crashed: " + r.stderr[-200:]
        # modules that fail even without the patch (e.g. need an installed sqlglot) prove nothing
        new_fail = sorted(failed - _baseline_failures())
        return bool(new_fail), ", ".join(new_fail)
    except subprocess.TimeoutExpired:
        return True, "timeout"
    finally:
        os.unlink(tmp)


# ---------------------------------------------------------------- compact map

def _map_digest(raw):
    import hashlib
    return hashlib.sha1(raw).hexdigest().encode()


def build_compact_map(map_path, out_path):
    """Image build step: the same map with each test set and each file's line table packed as
    uint32 arrays, so loading it is a memcpy and only the sets a commit touches get decoded."""
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
    """The JSON content of a gzip map file, from the build-time pickle of it (`--precompute`) when
    that was made from exactly this file (same bytes), else decoded here."""
    import pickle
    raw = Path(path).read_bytes()
    try:
        cached = (CACHE / (Path(path).name + ".pickle")).read_bytes()
        if cached[:40] == _map_digest(raw):
            return pickle.loads(cached[40:])
    except Exception:  # noqa: BLE001  no usable cache: decode the map itself
        pass
    return json.loads(gzip.decompress(raw).decode("utf-8"))


def build_map_pickle(path):
    import pickle
    raw = Path(path).read_bytes()
    m = json.loads(gzip.decompress(raw).decode("utf-8"))
    CACHE.mkdir(parents=True, exist_ok=True)
    (CACHE / (Path(path).name + ".pickle")).write_bytes(_map_digest(raw) + pickle.dumps(m, protocol=pickle.HIGHEST_PROTOCOL))


def _load_compact_map(map_path):
    """The compact copy when it was built from exactly this map file, else None."""
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



# ---------------------------------------------------------------- the selector

def lpt_pack(ms, chosen):
    """LPT on k <= 8 workers, k chosen to minimise max load + 2 s * k."""
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


# ---------------------------------------------------------------- R1 infection-witness map

R1 = os.environ.get("RWX_R1", "1") == "1"  # on by default; act only when no test is infected
R1_MODE = os.environ.get("RWX_R1_MODE", "empty")  # empty: act only when no test is infected
R1_MAP = Path(os.environ.get("RWX_R1_MAP", APP / "r1map.json.gz"))
_R1_OPS = [ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE, ast.Is, ast.IsNot, ast.In, ast.NotIn]


_R1_DEF = re.compile(r"^([ \t]*)(?:async[ \t]+)?def[ \t]")


def _indent(line):
    return len(line) - len(line.lstrip())


def operator_swaps(old_text, new_text):
    """operator_swaps_in on the smallest enclosing def of the changed lines (parsing a whole large
    module costs ~0.2 s); the whole file when that snippet cannot be isolated or parsed."""
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
    """If new_text differs from old_text only in the operator of single-operator comparisons or of
    whole boolean operations, return [(kind, "l:c:el:ec" of the old node, new op index)]; else None.
    kind 'c': Compare (op index into _R1_OPS); 'b': BoolOp (0 and, 1 or)."""
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
    """Cheap pre-check on the diff text: every removed line pairs with an added line that differs only
    in comparison/boolean operator tokens and whitespace. Only then are both files parsed."""
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
        self.sets, self.sites = [], {}  # a failed read leaves an empty map: every site is unknown -> fallback
        number = self.number
        m = _load_map_json(self.path)
        idx = [number.get(t) for t in m["tests"]]
        self.sets = [frozenset(idx[i] for i in s if idx[i] is not None) for s in m["sets"]]
        self.sites = m["sites"]
        self.skipped = {f: set(v) for f, v in m["skipped"].items()}
        self.missing = {number[t] for t in m["missing"] if t in number}

    def select(self, path, swaps):
        """Tests witnessing every swap, or None when the map cannot decide (fall back)."""
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
                return None  # witnessed while importing: every user of the module is exposed
            sid = alts.get(str(new_op if kind == "c" else 0), ex)
            out |= self.sets[sid]
        return out


class Selector:
    def __init__(self, map_path, tests):
        m = _load_compact_map(map_path)
        self.number = {t["id"]: t["number"] for t in tests}
        # the scorer's rounding: floor(seconds * 1000 + 0.5)
        self.ms = {t["number"]: math.floor(t["seconds"] * 1000 + 0.5) for t in tests}
        self.insurance = []  # per select(): unselected tests worth running for free, most plausible first
        self.all = set(self.ms)
        idx_to_num = [self.number.get(t) for t in (m or {}).get("tests", ())]
        if m is not None:  # build-time compact copy of this exact map: decode sets/lines on use
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
        if E1 and (APP / "e1map.json.gz").exists():
            try:
                import e1_cutoff
                self.e1 = e1_cutoff.Cutoff(APP / "e1map.json.gz", _load_map_json(APP / "e1map.json.gz"))
                self.e1_ids = {self.number[t]: t for t in self.e1.tests if t in self.number}
                self.e1_nums = set(self.e1_ids)
            except Exception:  # noqa: BLE001  E1 is optional: without it every test it would judge is kept
                self.e1, self.e1_nums, self.e1_ids = None, set(), {}
        self.r1 = WitnessMap(R1_MAP, self.number) if R1 and R1_MAP.exists() else None
        self.by_file = {}
        for t in tests:
            self.by_file.setdefault(t["file"], set()).add(t["number"])
        self._texts, self._scope_names, self._names_memo = {}, None, {}
        self.e2 = None
        if E2:
            try:
                self.e2 = self._e2_load()
            except Exception as e:  # no E2 map: v6 behaviour
                log(f"E2 map not loaded ({type(e).__name__}: {e})")

    # ------------------------------------------------------------------ E2 read map
    def _e2_load(self):
        if not (E2_MAP.exists() and E2_FP.exists() and E2_CANON.exists()):
            return None
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
        """Tests that looked `attr` up through class `cn` or a subclass. A receiver that is not a
        canonical class (built with type() at run time: several share one name, so its recorded MRO
        is ambiguous) counts as a subclass of everything."""
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
        """Lookups of module attribute `name` (present or not) through the module object, reads of
        the module's whole namespace, and every executed line of its own functions that loads it."""
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
        """Tests that read namespace change `ch` (from e2_ns diff), or None when the map cannot say."""
        loc, keys, status, ma, mb, ha, hb, override = ch
        e = self.e2
        oid = e["locs"].get(loc)
        cls_valued = any(isinstance(h, str) and h.startswith("T:") for h in (ha, hb))
        func = ma is not None or mb is not None
        if func and (status != "changed" or ma is None or mb is None):
            func = None  # function added or removed
        if loc.startswith("C|"):
            _, cn, attr = loc.split("|", 2)
            if attr.startswith("__") and attr.endswith("__") and attr != "__doc__":
                return None
            if f"C|{cn}|*" in e["skipped"] or cls_valued or func is None:
                return None
            if func:
                return self._e2_func_readers(ma)
            if loc in e["skipped"]:
                return None  # not instrumented
            if status == "added":
                # lookups through this class found the attribute on `override` before (a miss is
                # not recorded): known only when that base location was traced as a data value
                base = f"C|{override}|{attr}" if override else None
                if base is None or base not in e["locs"] or base in e["skipped"]:
                    return None
            if keys is not None and oid is not None:
                return self._e2_table_readers(oid, keys)
            return self._e2_attr_readers(cn, attr)
        _, mod, name = loc.split("|", 2)
        if f"G|{mod}|*" in e["skipped"] or (name.startswith("__") and name.endswith("__") and name != "__all__"):
            return None
        if func:
            return self._e2_func_readers(ma)
        if keys is not None and oid is not None and status == "changed":
            return self._e2_table_readers(oid, keys)
        out, ok = self._e2_global_readers(mod, name)
        return out if ok else None

    def e2_readers(self, e2_files, expect=None, add_only=False):
        """Namespace diff of the patched import, mapped to the tests that read what changed.
        (None, why) when anything is unclear: the caller then keeps the v6 selection."""
        import subprocess
        import tempfile
        mods = {}
        for rel, text in e2_files.items():
            name = rel[:-3].replace("/", ".")
            is_pkg = name.endswith(".__init__")
            if is_pkg:
                name = name[: -len(".__init__")]
            mods[name] = [text, is_pkg, str(SRC / rel).replace("\\", "/")]
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8") as fh:
            json.dump({"patched": mods}, fh)
            tmp = fh.name
        try:
            r = subprocess.run([sys.executable, "-I", "-S", str(APP / "e2_ns.py"), "diff", str(SRC), str(E2_FP), tmp],
                               capture_output=True, text=True, timeout=E2_TIMEOUT_S,
                               env={**os.environ, "PYTHONHASHSEED": "0"}, cwd=tempfile.gettempdir())
            out = json.loads(r.stdout.strip().splitlines()[-1])
        except Exception as ex:  # noqa: BLE001
            return None, f"diff failed ({type(ex).__name__})"
        finally:
            os.unlink(tmp)
        if "error" in out:
            return None, "diff error: " + out["error"][:200]
        if out.get("opaque") and not add_only:
            return None, f"opaque value in a patched module: {out['opaque'][0]}"
        changed = {c[0] for c in out["changes"]}
        for exact, prefixes in (expect or {}).values() if not add_only else ():
            miss = sorted(exact - changed) + sorted(p for p in prefixes if not any(c.startswith(p) for c in changed))
            if miss:
                return None, f"edit not seen by the diff: {miss[0]}"
        sel = set()
        for ch in out["changes"]:
            r = self.e2_change_readers(ch)
            if r is None and add_only:
                continue  # add-only: what is mapped is still worth adding
            if r is None:
                return None, f"unmapped change {ch[0]} ({ch[2]})"
            sel |= r
            if os.environ.get("RWX_E2_DEBUG"):
                log(f"  E2 {ch[0]} {ch[2]} keys={ch[1]} -> {len(r)}")
        # a changed entry of a table whose values name modules (MODULE_BY_DIALECT and the like) moves
        # a lazy import: the traced run had every module imported up front, so the lookups the lazy
        # path makes were never recorded. Select every user of each module named.
        for vals in out.get("strvals", {}).values():
            for v in vals:
                for f in self._e2_modules_named(v):
                    r = self.file_tests(f) | self.class_users(f, "<module>")
                    sel |= r
                    if os.environ.get("RWX_E2_DEBUG"):
                        log(f"  E2 lazy-import table names {f} -> {len(r)}")
        return sel, f"{len(out['changes'])} namespace changes"

    def _e2_modules_named(self, v):
        """sqlglot modules a table value names: a dotted module path, or a module's own name."""
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
        """Names a module loads while it is imported (import_scope_names), from the build-time
        index when its digest matches the pinned text, else computed here (None: unparseable)."""
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
        """Guard: a changed module-level name is read by other modules (`from X import NAME`,
        `X.NAME`). For every importer that mentions one of the names: a read inside a function
        selects the tests that ran that line; a read at import scope (module or class body) makes
        derived module state, so it selects every user of that importer; a test file: all its tests."""
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
        """Guard: function `fname` of `path` runs while a lazily imported module (one not imported
        at collection) is imported inside some test. Its result is shared by every user of that
        module, but the map credits its lines only to the first importer: users of each such module."""
        out = set()
        for f in {path, *self.importers.get(path, ())}:  # the module and its direct importers
            if f.endswith(".py") and f not in self.collect:
                n = self.import_names(f)
                if n is None or fname in n:
                    out |= self.file_tests(f) | self.class_users(f, "<module>")
        return out

    def package_tests(self, path):
        """Every test file in the package (directory) of a tests/ helper or __init__ module."""
        pre = path.rsplit("/", 1)[0] + "/"
        out = set()
        for f, nums in self.by_file.items():
            if f.startswith(pre):
                out |= nums
        return out

    def dir_openers(self, path):
        """Guard: a new file in a directory that tests enumerate: the tests that opened the
        directory (or an ancestor of it) or any file next to it."""
        parent = path.rsplit("/", 1)[0] if "/" in path else ""
        out = set()
        for k, sid in self.opened.items():
            kp = k.rsplit("/", 1)[0] if "/" in k else ""
            if (k != path and kp == parent) or path.startswith(k.rstrip("/") + "/"):
                out |= self.sets[sid]
        return out

    def dir_mentions(self, path):
        """Guard: a non-Python file in a top-level directory that is not a Python package (build
        and packaging trees such as sqlglotc/): the test files that refer to that directory."""
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
        """Tests that used class `qualname` of module `path` (or any class of it, for module scope)."""
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
        """path plus every file that imports it, directly or transitively (static graph)."""
        seen, todo = {path}, [path]
        while todo:
            for imp in self.importers.get(todo.pop(), ()):
                if imp not in seen:
                    seen.add(imp)
                    todo.append(imp)
        return seen

    def broken_module_tests(self, paths):
        """A module that cannot be imported breaks every importer: select all their users. When any
        of them is imported at collection time, test files can fail to collect through imports the
        static graph cannot see (lazy module __getattr__), so select everything."""
        files = set()
        for p in paths:
            files |= self.import_closure(p)
        if "sqlglot/__init__.py" in files or any(f in self.collect for f in files):
            return set(self.all), files
        sel = set()
        for f in files:
            sel |= self.file_tests(f) | self.class_users(f, "<module>")
        return sel, files

    def file_tests(self, path):
        sel = self.touching(path)
        if path in self.opened:
            sel |= self.sets[self.opened[path]]
        sel |= self.by_file.get(path, set())
        return sel

    def select(self, patch_text, allow_probe=True):
        why = []
        # insurance tiers, most plausible first: the whole edited function (statement narrowing
        # dropped these), any line of the edited file, users of the edited module's classes
        self.insurance = tiers = [set(), set(), set()]
        try:
            files = parse_patch(patch_text)
        except Exception as e:  # unparseable: be safe
            return set(self.all), [f"unparseable patch: {e}"]
        if not files:
            return set(), ["empty patch"]
        chosen = set()
        e2_fallback, e2_files, e2_block, e2_expect = set(), {}, False, {}
        e2_bind = False  # a module's set of bound names changed: registries scan namespaces
        e1_soft, e1_files = [], {}  # E1: (path, ranges, deferred tests) per function edit; patched sources
        scope_changed = {}  # sqlglot module path -> new source, for the import check
        for f in files:
            old, new = f["old"], f["new"]
            path = old or new
            if f["binary"]:
                chosen |= self.file_tests(path)
                why.append(f"{path}: binary -> file tests")
                continue
            if path in CONFIG_FILES or Path(path).name == "conftest.py":
                why.append(f"{path}: test configuration -> all")
                return set(self.all), why
            if old is None or new is None or new != old:
                e2_block = True  # new, deleted or renamed files: the namespace diff does not model them
            if old is None:  # new file: nothing can depend on it unless another file changes too
                if importable(new):
                    try:  # but it can shadow or break an import: include it in the import check
                        scope_changed[new] = apply_hunks("", f["hunks"])[0]
                    except ValueError:
                        pass
                sel = self.dir_openers(new) | (set() if new.endswith(".py") else self.dir_mentions(new))
                chosen |= sel
                why.append(f"{new}: new file -> directory openers {len(sel)}")
                continue
            src = SRC / old
            if not src.exists():
                why.append(f"{old}: not in pinned tree -> none")
                continue
            old_text = src.read_text(encoding="utf-8")
            if new is None or (new != old and old.endswith(".py")):
                # deleted, or a renamed module: importers of the old path break
                sel, files_ = self.broken_module_tests([old]) if old.endswith(".py") else (self.file_tests(old), {old})
                chosen |= sel
                why.append(f"{old}: {'deleted' if new is None else 'renamed'} -> {len(sel)}")
                continue
            try:
                new_text, changed, inserts = apply_hunks(old_text, f["hunks"])
            except ValueError as e:
                sel = self.broken_module_tests([old])[0] if old.endswith(".py") else self.file_tests(old)
                chosen |= sel
                why.append(f"{old}: hunks do not apply ({e}) -> {len(sel)}")
                continue
            if new != old:  # rename of a data file: references to the old path break
                chosen |= self.file_tests(old)
            if not old.endswith(".py"):
                sel = set()
                if old in self.opened:
                    sel = set(self.sets[self.opened[old]])
                sel |= self.dir_mentions(old)
                chosen |= sel
                why.append(f"{old}: data file -> openers {len(sel)}")
                continue
            status, regions = code_changes(old, old_text, new_text, f["hunks"])
            e1_files[old] = new_text
            if status == "null":
                why.append(f"{old}: bytecode-identical -> none")
                continue
            if status == "syntax":
                sel, files_ = self.broken_module_tests([old])
                chosen |= sel
                why.append(f"{old}: syntax error -> users of it and its {len(files_) - 1} importers: {len(sel)}")
                continue
            r1_sel = None
            try:
                if self.r1 is not None and old.startswith("sqlglot/") and maybe_operator_swap(f["hunks"]):
                    # R1: the file's ONLY change is mapped operator swaps. When no evaluation anywhere in
                    # the suite is infected by them (RWX_R1_MODE=empty), no test can see them: the
                    # line-coverage selection for the file is empty. The guards below still widen.
                    swaps = operator_swaps(old_text, new_text)
                    r1_sel = self.r1.select(old, swaps) if swaps else None
                    if r1_sel is not None:
                        # tests without a witness record: keep the ones that ran the file
                        r1_sel |= self.touching(old) & self.r1.missing
                    if r1_sel and R1_MODE != "partial":
                        # some test was infected: a later test can reuse state the infected evaluation
                        # left behind (module-level memo tables), so per-test attribution is not safe.
                        why.append(f"{old}: operator swap witnessed by {len(r1_sel)} tests -> regions")
                        r1_sel = None
                    if r1_sel is not None:
                        why.append(f"{old}: {len(swaps)} operator swap(s) -> witnesses {len(r1_sel)}")
            except Exception:  # noqa: BLE001  R1 is optional: on any failure the file gets the v7d selection
                r1_sel = None
            sel = set() if r1_sel is None else set(r1_sel)
            tiers[1] |= self.file_tests(old)
            tiers[2] |= self.class_users(old, "<module>")
            col = self.collect.get(old, set())
            if regions and importable(old) and old not in self.collect:
                # Never imported at collection: tests import it lazily (a dialect loaded inside a
                # test), so its import-time code, including functions its module or class bodies
                # call, ran inside some test and is not in `collect`. Any code change may then crash
                # the import: probe it.
                scope_changed[old] = new_text
            narrowed = 0
            e2_ok = E2 and old.startswith("sqlglot/") and self.e2 is not None
            e2_prune = e2_ok and E2_PRUNE
            for kind, ranges, qualname, (lo, hi), own in regions:
                ran_at_import = kind == "func" and bool(own & col)
                at_import = ran_at_import
                if at_import and FRAME_DIFF and ranges != [(lo, hi)]:
                    # collection ran this function but none of its divergent statements: collection
                    # is unchanged, so the function narrows like any other
                    at_import = any(a <= ln <= b for ln in col for a, b in ranges)
                    if not at_import and importable(old):
                        scope_changed[old] = new_text  # keep the import probe all the same
                if at_import or ranges == [(lo, hi)]:
                    # a function that ran at import time shares its results with every user of the
                    # module: no statement narrowing for it
                    ranges = [(lo, hi)]
                else:
                    narrowed += 1
                hit = set()
                for a, b in ranges if r1_sel is None else ():  # R1 decided the file's covered tests
                    hit |= self.touching(old, a, b)
                if self.e1 and r1_sel is None and kind == "func" and not at_import and old.startswith("sqlglot/"):
                    e1_soft.append((old, ranges, hit & self.e1_nums))
                    hit = hit - self.e1_nums  # decided after the loop, by the boundary check
                sel |= hit
                if ranges != [(lo, hi)]:
                    tiers[0] |= self.touching(old, lo, hi)
                if at_import:
                    if importable(old):
                        scope_changed[old] = new_text  # it can crash the import: probe it
                    if not hit:
                        # only ever ran at import time: its effect reaches the module's users
                        kind, qualname = "scope", "<module>"
                        sel |= self.touching(old)
                if kind == "func" and "." not in qualname and not at_import:
                    sel |= self.lazy_import_users(old, qualname)
                if IMPORT_TIME_RULE and at_import:
                    kind, qualname = "scope", "<module>"
                if kind == "scope":
                    # class body / module level: constants and tables are read by shared code, so
                    # also every test that used the class (or any class of the module).
                    wide = self.class_users(old, qualname)
                    if e2_prune and not at_import:
                        # E2 may replace the class users and the body's line span by the readers
                        # of what the body changed; kept as the fallback
                        e2_fallback |= wide
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
                helper = old.startswith("tests/") and not Path(old).name.startswith("test_")
                if helper and effects:
                    # a side effect at the top of a test helper / package __init__ (imported at
                    # collection) changes the process every later test runs in
                    why.append(f"{old}: module-level side effect in a test helper -> all")
                    return set(self.all), why
                if names is None:
                    sel |= set(self.all)
                else:
                    if helper and names:
                        sel |= self.package_tests(old)
                    nr = self.name_readers(old, names)
                    if e2_prune:
                        e2_fallback |= nr - sel  # other modules' reads show in the namespace diff
                    else:
                        sel |= nr
            chosen |= sel
            if e2_ok:
                e2_files[old] = new_text
                e2_expect[old] = e2_expected(old, old_text, new_text)
                if e2_expect[old] is None:
                    e2_block = True
            else:
                e2_block = True
            why.append(f"{old}: {len(regions)} changed code regions ({narrowed} statement-level) -> {len(sel)}")
        if scope_changed:
            # Import-time code changed: valid syntax can still crash at import (NameError, bad table
            # entry), which fails every test that imports the module. Check it for real, unless the
            # run is short of time: then assume the worst.
            closure = set()
            for p in scope_changed:
                closure |= self.import_closure(p)
            probe = sorted(f for f in closure if importable(f))
            if allow_probe:
                failed, detail = import_fails(SRC, scope_changed, probe)
            else:
                failed, detail = True, "probe skipped: run deadline"
            if failed and (not allow_probe or detail == "timeout" or detail.startswith("probe crashed")):
                # no verdict (deadline, hang, crashed probe): an import that hangs or dies can take
                # down whole workers, so assume the worst
                why.append(f"import check gave no verdict ({detail.strip().splitlines()[-1:]}) -> all")
                return set(self.all), why
            if failed:
                broken = {p for p in scope_changed if (SRC / p).exists()}
                for name in detail.split(", ") if allow_probe else ():
                    # modules that failed to import (a new module can break `import sqlglot`)
                    for rel in (name.replace(".", "/") + ".py", name.replace(".", "/") + "/__init__.py"):
                        if (SRC / rel).exists():
                            broken.add(rel)
                sel, files_ = self.broken_module_tests(sorted(broken))
                chosen |= sel
                why.append(f"import fails ({detail.strip().splitlines()[-1:]}) -> users of {len(files_)} modules: {len(sel)}")
            else:
                why.append("import check ok")
                failed = False
        else:
            failed = False
        if E2 and self.e2 is not None and not E2_PRUNE:
            # g8, add-only: registry / namespace-membership consumers of a binding change
            if e2_bind and not failed and not e2_block and allow_probe:
                e2sel, detail = self.e2_readers(e2_files, e2_expect, add_only=True)
                why.append(f"g8: {detail}")
                if e2sel:
                    chosen |= e2sel
                    why.append(f"g8 adds readers {len(e2sel)}")
        elif E2 and self.e2 is not None and (e2_fallback - chosen or e2_bind):
            # also when nothing would be pruned: a changed binding (an import or a name added /
            # removed / rebound at module level) reaches namespace-scanning registries
            # (subclasses(__name__, ...), module __getattr__, name-keyed tables), and the diff
            # shows the derived registry entries and the tests that read them
            e2sel = None
            # the diff costs ~E2_COST_MS of CPU; the extra tests cost roughly their time spread over
            # the workers: skip the diff when it is unlikely to pay for itself (the fallback is a
            # superset, so this only trades cost, never safety)
            gain = sum(self.ms[n] for n in e2_fallback - chosen) / MAX_WORKERS
            if gain < E2_COST_MS and not e2_bind:
                why.append(f"E2 skipped: at most {gain:.0f} ms to gain")
            elif not failed and not e2_block and allow_probe:
                e2sel, detail = self.e2_readers(e2_files, e2_expect)
                why.append(f"E2: {detail}")
            if e2sel is None:
                chosen |= e2_fallback
                why.append(f"E2 fallback -> {len(e2_fallback)}")
            else:
                chosen |= e2sel
                why.append(f"E2 readers {len(e2sel)} instead of {len(e2_fallback)}")
        if e1_soft:
            chosen |= self.e1_check(e1_soft, e1_files, chosen, why)
        if chosen and self.untraced:
            chosen |= self.untraced
        return chosen, why

    def e1_check(self, soft, files, hard, why):
        """Deferred E1 tests to keep: all of them, except those whose only reasons are edits that
        run in the compile phase alone and leave every boundary fingerprint unchanged."""
        wants = {}
        for path, ranges, tests in soft:
            for n in tests - hard:
                wants.setdefault(self.e1_ids[n], []).append((path, ranges))
        if not wants or self.e1_spent > E1_BUDGET_S:
            return {self.number[tid] for tid in wants}
        t = time.monotonic()
        dropped = self.e1.droppable(SRC, files, wants)
        self.e1_spent += time.monotonic() - t
        why.append(f"E1 {len(dropped)}/{len(wants)} dropped ({time.monotonic() - t:.1f}s): {sorted(dropped)}")
        return {self.number[tid] for tid in wants if tid not in dropped}

    def pack(self, chosen):
        if not chosen:
            return []
        return self.fill(lpt_pack(self.ms, chosen), chosen)

    def fill(self, bins, chosen):
        """Free insurance: the cost is the busiest worker's load plus 2 s per worker, so room on the
        other workers up to that load costs nothing. Fill it with the most plausible unselected
        tests (insurance tiers in order, shortest first within a tier). Never adds a worker."""
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


def precompute():
    import hashlib
    import marshal
    try:
        build_compact_map(MAP, CACHE / "map.bin")
    except Exception as e:
        log(f"compact map not built ({type(e).__name__}: {e}): the gzip JSON map will be used")
    for p in (APP / "e1map.json.gz", E2_MAP, R1_MAP):  # decoded-map pickles (checked on use)
        try:
            build_map_pickle(p)
        except Exception as e:  # noqa: BLE001
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
    (CACHE / "import_names.json").write_text(json.dumps(idx), encoding="utf-8")
    log(f"precompute: compact map, {n} compiled pinned files, {len(idx)} import-scope name sets")








GC_VALVE_MB = 1500


def _maxrss_mb():
    try:
        import resource
        return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024
    except Exception:  # no resource module: keep the collector on
        return float("inf")


def main():
    if sys.argv[1:] == ["--baseline"]:  # image build step
        base = sorted(_probe_all())
        (APP / "import_baseline.json").write_text(json.dumps(base), encoding="utf-8")
        log(f"import baseline: {len(base)} modules fail without any patch: {base}")
        return
    if sys.argv[1:] == ["--precompute"]:  # image build step: caches that are verified on every use
        precompute()
        return
    t0 = time.monotonic()
    # CPU: the cyclic collector rescans the loaded maps and every parsed tree over and over (~1/4 of
    # this process's CPU on s1); nothing here depends on when cycles are freed. Memory stays well
    # inside the limit (s1: 0.3 -> 0.55 GB); past GC_VALVE_MB the collector is switched back on.
    gc.disable()
    tests = json.loads((DATA / "tests.json").read_text(encoding="utf-8"))["tests"]
    patches = sorted((DATA / "commits").glob("*.patch"))
    out_lock, done = threading.Lock(), set()

    def watchdog():
        # selection overran: answer every remaining commit with the whole suite (a superset of any
        # selection, so still safe) and exit inside the limit
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
    for i, patch in enumerate(patches):
        text = patch.read_text(encoding="utf-8", errors="replace")
        # time check: stop probing once the spent time, or the projection of the mean time per
        # commit so far over the remaining commits, passes the safe fraction of the run limit
        spent = time.monotonic() - t0 - sel.e1_spent  # E1 has its own budget
        projected = spent + (spent / i) * (len(patches) - i) if i else spent
        allow_probe = max(spent, projected) < SAFE_FRACTION * RUN_LIMIT_S
        try:
            chosen, why = sel.select(text, allow_probe=allow_probe)
        except Exception as e:  # never crash the batch: run everything for this commit
            chosen, why = set(sel.all), [f"selector error {type(e).__name__}: {e}"]
        workers = sel.pack(chosen)
        with out_lock:
            sys.stdout.write(json.dumps({"commit": patch.stem, "workers": workers}) + "\n")
            sys.stdout.flush()
            done.add(patch.stem)
        log(f"{patch.stem}: {len(chosen)} tests, {len(workers)} workers | " + "; ".join(why))
        if not gc.isenabled() and _maxrss_mb() > GC_VALVE_MB:
            gc.enable()
            gc.collect()
    timer.cancel()
    sys.stdout.flush()
    _close_probe_server()
    t = os.times()
    log(f"CPU self user+sys {t.user + t.system:.3f}s children {t.children_user + t.children_system:.3f}s")


if __name__ == "__main__":
    main()
