"""Blast Radius selector: for each patch, choose the tests that can catch it and pack them on workers.

Pipeline per commit (each stage only handles what the earlier, cheaper ones could not settle):
  1. Parse the unified diff and rebuild each changed file's new text in memory.
  2. Null-perturbation check (.py): compile old and new; code objects identical apart from line
     numbers => the change cannot alter behavior => contributes no tests.
  3. Exposure (.py): for each code object whose own code changed, the tests that executed any line
     of it at the pinned commit (per-test trace map). Added/removed code charges its enclosing scope.
  4. Non-code files: tests that opened the file during the traced run (fixtures).
  5. Anything the map cannot reason about (syntax errors in imported modules, test configuration,
     unparseable patches) falls back to a wider, safe set.
  6. Pack the chosen tests on k <= 8 workers (LPT), choosing k to minimise max load + 2 s * k.
Logs go to stderr; stdout carries exactly one JSON line per commit.
"""
import gzip
import json
import os
import re
import sys
import types
from pathlib import Path

APP = Path(__file__).resolve().parent
DATA = Path(os.environ.get("RWX_DATA", "/data"))
SRC = Path(os.environ.get("RWX_SRC", APP / "sqlglot"))
MAP = Path(os.environ.get("RWX_MAP", APP / "map.json.gz"))
MAX_WORKERS = 8
WORKER_COST_MS = 2000

CONFIG_FILES = {"conftest.py", "tests/conftest.py", "setup.cfg", "pytest.ini", "tox.ini", "pyproject.toml"}


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
                i += 1
                while i < len(lines):
                    l2 = lines[i]
                    if l2.startswith((" ", "+", "-")) or l2 == "":
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


def _own_signature(co):
    consts = tuple(_canon(c) for c in co.co_consts)
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


_compiled = {}


def compile_old(path, text):
    co = _compiled.get(path)
    if co is None:
        co = _compiled[path] = compile(text, path, "exec", dont_inherit=True)
    return co


def code_changes(path, old_text, new_text):
    """Return ('null', []) | ('syntax', []) | ('changed', [(kind, (lo, hi))...]).
    kind is 'func' for a function-like code object, 'scope' for a module or class body."""
    try:
        new_co = compile(new_text, path, "exec", dont_inherit=True)
    except (SyntaxError, ValueError):
        return "syntax", []
    old_co = compile_old(path, old_text)
    old_map, new_map = _walk(old_co, "", {}), _walk(new_co, "", {})
    regions = []

    def scope_of(key):
        # parent key of a code object
        return key.rsplit("/", 1)[0] if "/" in key else ""

    def kind(co):
        return "func" if co.co_flags & 0x0002 else "scope"  # CO_NEWLOCALS: functions, lambdas, comprehensions

    for key, oco in old_map.items():
        nco = new_map.get(key)
        if nco is None:
            regions.append((kind(oco), _span(oco), oco.co_qualname))
            parent = old_map.get(scope_of(key))
            if parent is not None and key:
                regions.append((kind(parent), _span(parent), parent.co_qualname))
        elif _own_signature(oco) != _own_signature(nco):
            regions.append((kind(oco), _span(oco), oco.co_qualname))
    for key in new_map:
        if key not in old_map:
            # added code: charge the nearest existing ancestor scope
            k = scope_of(key)
            while k not in old_map and k:
                k = scope_of(k)
            parent = old_map.get(k, old_co)
            regions.append((kind(parent), _span(parent), parent.co_qualname))
    if not regions:
        return "null", []
    return "changed", regions


# ---------------------------------------------------------------- import check

_IMPORT_PROBE = r"""
import importlib.abc, importlib.util, json, sys
patched = json.load(open(sys.argv[1], encoding="utf-8"))  # {module name: source}
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
        exec(compile(src, origin, "exec"), module.__dict__)
sys.path.insert(0, root)
sys.meta_path.insert(0, Finder())
import sqlglot
for name in patched:
    importlib.import_module(name)
"""


def import_fails(src_root, patched_files):
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
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8") as fh:
        json.dump(mods, fh)
        tmp = fh.name
    try:
        r = subprocess.run([sys.executable, "-I", "-S", "-c", _IMPORT_PROBE, tmp, str(src_root)],
                           capture_output=True, text=True, timeout=60)
        return r.returncode != 0, r.stderr[-300:]
    except subprocess.TimeoutExpired:
        return True, "timeout"
    finally:
        os.unlink(tmp)


# ---------------------------------------------------------------- the selector

class Selector:
    def __init__(self, map_path, tests):
        with gzip.open(map_path, "rt", encoding="utf-8") as fh:
            m = json.load(fh)
        self.number = {t["id"]: t["number"] for t in tests}
        self.ms = {t["number"]: round(t["seconds"] * 1000) for t in tests}
        self.all = set(self.ms)
        idx_to_num = [self.number.get(t) for t in m["tests"]]
        self.sets = [frozenset(idx_to_num[i] for i in s if idx_to_num[i] is not None) for s in m["sets"]]
        self.lines = {f: {int(ln): sid for ln, sid in d.items()} for f, d in m["lines"].items()}
        self.opened = m["opened"]
        self.collect = {f: set(v) for f, v in m["collect"].items()}
        self.classes = m.get("classes", {})
        traced_ids = set(m["tests"]) - set(m["missing"])
        self.untraced = {t["number"] for t in tests if t["id"] not in traced_ids}
        self.by_file = {}
        for t in tests:
            self.by_file.setdefault(t["file"], set()).add(t["number"])

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

    def file_tests(self, path):
        sel = self.touching(path)
        if path in self.opened:
            sel |= self.sets[self.opened[path]]
        sel |= self.by_file.get(path, set())
        return sel

    def select(self, patch_text):
        why = []
        try:
            files = parse_patch(patch_text)
        except Exception as e:  # unparseable: be safe
            return set(self.all), [f"unparseable patch: {e}"]
        if not files:
            return set(), ["empty patch"]
        chosen = set()
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
            if old is None:  # new file: nothing can depend on it unless another file changes too
                why.append(f"{new}: new file -> none")
                continue
            src = SRC / old
            if not src.exists():
                why.append(f"{old}: not in pinned tree -> none")
                continue
            old_text = src.read_text(encoding="utf-8")
            if new is None:  # deleted
                sel = self.file_tests(old)
                if old in self.collect:
                    why.append(f"{old}: deleted, imported at collection -> all")
                    return set(self.all), why
                chosen |= sel
                why.append(f"{old}: deleted -> {len(sel)}")
                continue
            try:
                new_text, changed, inserts = apply_hunks(old_text, f["hunks"])
            except ValueError as e:
                sel = self.file_tests(old)
                chosen |= sel
                why.append(f"{old}: hunks do not apply ({e}) -> file tests {len(sel)}")
                continue
            if new != old:  # rename: references to the old path break
                chosen |= self.file_tests(old)
            if not old.endswith(".py"):
                sel = set()
                if old in self.opened:
                    sel = set(self.sets[self.opened[old]])
                chosen |= sel
                why.append(f"{old}: data file -> openers {len(sel)}")
                continue
            status, regions = code_changes(old, old_text, new_text)
            if status == "null":
                why.append(f"{old}: bytecode-identical -> none")
                continue
            if status == "syntax":
                if old in self.collect:
                    why.append(f"{old}: syntax error in a module imported at collection -> all")
                    return set(self.all), why
                sel = self.file_tests(old) | self.class_users(old, "<module>")
                chosen |= sel
                why.append(f"{old}: syntax error -> file tests + class users {len(sel)}")
                continue
            sel = set()
            for kind, (lo, hi), qualname in regions:
                sel |= self.touching(old, lo, hi)
                if kind == "scope":
                    # class body / module level: constants and tables are read by shared code, so
                    # also every test that used the class (or any class of the module).
                    sel |= self.class_users(old, qualname)
                    if old.startswith("sqlglot/"):
                        scope_changed[old] = new_text
                    if old.startswith("tests/"):
                        sel |= self.by_file.get(old, set())
            chosen |= sel
            why.append(f"{old}: {len(regions)} changed code regions -> {len(sel)}")
        if scope_changed:
            # Import-time code changed: valid syntax can still crash at import (NameError, bad table
            # entry), which fails every test that imports the module. Check it for real.
            failed, detail = import_fails(SRC, scope_changed)
            if failed:
                if any(p in self.collect for p in scope_changed):
                    why.append(f"import of patched module fails ({detail.strip().splitlines()[-1:]}) -> all")
                    return set(self.all), why
                for p in scope_changed:
                    chosen |= self.file_tests(p) | self.class_users(p, "<module>")
                why.append("import of patched lazily-loaded module fails -> its users")
            else:
                why.append("import check ok")
        if chosen and self.untraced:
            chosen |= self.untraced
        return chosen, why

    def pack(self, chosen):
        if not chosen:
            return []
        order = sorted(chosen, key=lambda n: (-self.ms[n], n))
        best = None
        for k in range(1, min(MAX_WORKERS, len(order)) + 1):
            loads, bins = [0] * k, [[] for _ in range(k)]
            for n in order:
                j = loads.index(min(loads))
                bins[j].append(n)
                loads[j] += self.ms[n]
            cost = max(loads) + WORKER_COST_MS * k
            if best is None or cost < best[0]:
                best = (cost, bins)
        return best[1]


def main():
    tests = json.loads((DATA / "tests.json").read_text(encoding="utf-8"))["tests"]
    sel = Selector(MAP, tests)
    for patch in sorted((DATA / "commits").glob("*.patch")):
        text = patch.read_text(encoding="utf-8", errors="replace")
        try:
            chosen, why = sel.select(text)
        except Exception as e:  # never crash the batch: run everything for this commit
            chosen, why = set(sel.all), [f"selector error {type(e).__name__}: {e}"]
        workers = sel.pack(chosen)
        sys.stdout.write(json.dumps({"commit": patch.stem, "workers": workers}) + "\n")
        log(f"{patch.stem}: {len(chosen)} tests, {len(workers)} workers | " + "; ".join(why))
    sys.stdout.flush()
    t = os.times()
    log(f"CPU self user+sys {t.user + t.system:.3f}s children {t.children_user + t.children_system:.3f}s")


if __name__ == "__main__":
    main()
