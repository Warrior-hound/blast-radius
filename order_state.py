'usage: python order_state.py build SRC_ROOT MAP_JSON_GZ OUT_JSON [E2MAP_JSON_GZ]'














import ast
import gzip
import importlib
import json
import os
import sys
import types

MUTATORS = {"clear", "pop", "popitem", "update", "setdefault", "append", "extend", "insert", "remove",
            "add", "discard", "sort", "reverse", "__setitem__", "__delitem__"}
SELFLIKE = {"self", "cls", "mcs", "klass"}


def _pytest_key(path):

    return tuple(path.split("/"))


def _is_ours(obj):
    if isinstance(obj, types.ModuleType):
        return (obj.__name__ or "").split(".")[0] == "sqlglot"
    if isinstance(obj, type):
        return (getattr(obj, "__module__", "") or "").split(".")[0] == "sqlglot"
    return False


def _aliases(tree):

    out = {}
    for n in ast.walk(tree):
        if isinstance(n, ast.Import):
            for a in n.names:
                if a.name.split(".")[0] != "sqlglot":
                    continue
                try:
                    if a.asname:
                        out[a.asname] = importlib.import_module(a.name)
                    else:
                        importlib.import_module(a.name)
                        out[a.name.split(".")[0]] = importlib.import_module("sqlglot")
                except Exception:
                    pass
        elif isinstance(n, ast.ImportFrom) and n.level == 0 and (n.module or "").split(".")[0] == "sqlglot":
            try:
                mod = importlib.import_module(n.module)
            except Exception:
                continue
            for a in n.names:
                obj = getattr(mod, a.name, None)
                if obj is None:
                    try:
                        obj = importlib.import_module(f"{n.module}.{a.name}")
                    except Exception:
                        obj = None
                if obj is not None and _is_ours(obj):
                    out[a.asname or a.name] = obj
    return out


def _resolve(expr, al):
    if isinstance(expr, ast.Name):
        return al.get(expr.id)
    if isinstance(expr, ast.Attribute):
        base = _resolve(expr.value, al)
        if base is None:
            return None
        obj = getattr(base, expr.attr, None)
        return obj if obj is not None and _is_ours(obj) else None
    return None


def _target(expr, al):

    while isinstance(expr, ast.Subscript):
        expr = expr.value
    if isinstance(expr, ast.Attribute):
        owner = _resolve(expr.value, al)
        if owner is not None:
            return owner, expr.attr
    return None


def _restored_ids(tree, al):



    out = set()
    for blk in ast.walk(tree):
        for field in ("body", "orelse", "finalbody", "handlers"):
            stmts = getattr(blk, field, None)
            if not isinstance(stmts, list):
                continue
            for i, t in enumerate(stmts):
                if not isinstance(t, ast.Try) or not t.finalbody:
                    continue
                undo = {k[:2] for k, _ in _mutation_nodes(ast.Module(body=t.finalbody, type_ignores=[]), al)}
                for part in (stmts[:i], t.body, t.finalbody):
                    for k, n in _mutation_nodes(ast.Module(body=part, type_ignores=[]), al):
                        if k[:2] in undo:
                            out.add(id(n))
    return out


def _key_of(n):
    return n.value if isinstance(n, ast.Constant) and isinstance(n.value, str) else None


def _mutation_nodes(tree, al):


    out = []

    def add(t, n, key=None):
        if t is not None:
            out.append(((t[0], t[1], key if t[1] == "__dict__" else None), n))
    for n in ast.walk(tree):
        if isinstance(n, ast.Call):
            f = n.func
            if isinstance(f, ast.Attribute) and f.attr in MUTATORS:
                add(_target(f.value, al), n, _key_of(n.args[0]) if n.args else None)
            elif (isinstance(f, ast.Name) and f.id in ("setattr", "delattr") and len(n.args) >= 2
                  and isinstance(n.args[1], ast.Constant) and isinstance(n.args[1].value, str)):
                owner = _resolve(n.args[0], al)
                if owner is not None:
                    out.append(((owner, n.args[1].value, None), n))
        elif isinstance(n, (ast.Assign, ast.AugAssign, ast.AnnAssign, ast.Delete)):
            ts = n.targets if isinstance(n, (ast.Assign, ast.Delete)) else [n.target]
            for t in ts:
                for e in (t.elts if isinstance(t, (ast.Tuple, ast.List)) else [t]):
                    add(_target(e, al), n, _key_of(e.slice) if isinstance(e, ast.Subscript) else None)
    return out


def mutations(tree):

    al = _aliases(tree)
    skip = _restored_ids(tree, al)
    return {k for k, n in _mutation_nodes(tree, al) if id(n) not in skip}


def _owner_name(owner):
    if isinstance(owner, types.ModuleType):
        return owner.__name__
    return f"{owner.__module__}:{owner.__qualname__}"


def _owner_file(owner, root):
    mod = owner if isinstance(owner, types.ModuleType) else sys.modules.get(owner.__module__)
    f = getattr(mod, "__file__", None)
    if not f:
        return None
    return os.path.relpath(os.path.realpath(f), root).replace(os.sep, "/")


def _functions(tree):

    out = []

    def walk(node, fn):
        for c in ast.iter_child_nodes(node):
            cf = c if isinstance(c, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)) else fn
            if cf is not None:
                out.append((cf, c))
            walk(c, cf)
    walk(tree, None)
    return out


def reach_spans(root, owner, attr, sources):



    ofile = _owner_file(owner, root)
    is_mod = isinstance(owner, types.ModuleType)
    spans = {}
    for rel, tree in sources.items():
        al = _aliases(tree) if is_mod else {}
        hit = set()
        if is_mod and attr == "__dict__":
            if rel == ofile:
                for fn, n in _functions(tree):
                    if (isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "globals") or (
                            n is fn and getattr(fn, "name", "") == "__getattr__"):
                        hit.add(fn)
        else:
            for fn, n in _functions(tree):
                if isinstance(n, ast.Attribute) and n.attr == attr:
                    if not is_mod:
                        hit.add(fn)
                    elif isinstance(n.value, ast.Name) and (al.get(n.value.id) is owner):
                        hit.add(fn)
                elif is_mod and rel == ofile and isinstance(n, ast.Name) and n.id == attr:
                    hit.add(fn)
        for fn in hit:
            lo = min([fn.lineno] + [d.lineno for d in getattr(fn, "decorator_list", [])])
            spans.setdefault(rel, set()).add((lo, fn.end_lineno))
    return {f: sorted(v) for f, v in spans.items()}


def build(root, map_path, out_path, e2_path=None):
    root = os.path.realpath(root)
    sys.path.insert(0, root)
    with gzip.open(map_path, "rt", encoding="utf-8") as fh:
        m = json.load(fh)
    e2 = None
    if e2_path and os.path.exists(e2_path):
        with gzip.open(e2_path, "rt", encoding="utf-8") as fh:
            e2 = json.load(fh)
    tests = m["tests"]
    files = sorted({t.split("::")[0] for t in tests}, key=_pytest_key)
    pos = {f: i for i, f in enumerate(files)}
    test_files, sources = {}, {}
    for base in ("tests", "sqlglot"):
        for dp, dns, fns in os.walk(os.path.join(root, base)):
            dns[:] = sorted(d for d in dns if d != "__pycache__")
            for fn in sorted(fns):
                if not fn.endswith(".py"):
                    continue
                rel = os.path.relpath(os.path.join(dp, fn), root).replace(os.sep, "/")
                try:
                    tree = ast.parse(open(os.path.join(root, rel), encoding="utf-8").read())
                except SyntaxError:
                    continue
                (test_files if base == "tests" else sources)[rel] = tree
    groups = []
    for rel in sorted(test_files, key=_pytest_key):
        muts = mutations(test_files[rel])
        if not muts:
            continue

        start = pos.get(rel, 0)
        later = {t for t in tests if pos[t.split("::")[0]] >= start}
        by = {}
        for owner, attr, key in muts:
            by.setdefault((owner, attr), set()).add(key)
        for (owner, attr), keys in sorted(by.items(), key=lambda kv: (_owner_name(kv[0][0]), kv[0][1])):
            spans = reach_spans(root, owner, attr, sources)




            def post_only(f, a, b):
                col = set(m["collect"].get(f, ()))
                for ln, sid in m["lines"].get(f, {}).items():
                    ln = int(ln)
                    if a <= ln <= b and ln not in col and m["sets"][sid] and all(
                            tests[i] in later for i in m["sets"][sid]):
                        return True
                return False
            touch = spans
            spans = {f: [(a, b) for a, b in ss if post_only(f, a, b)] for f, ss in spans.items()}
            spans = {f: ss for f, ss in spans.items() if ss}
            readers = set()
            for f, ss in touch.items():
                for ln, sid in m["lines"].get(f, {}).items():
                    if any(a <= int(ln) <= b for a, b in ss):
                        readers |= {tests[i] for i in m["sets"][sid]} & later
            if attr == "__dict__" and isinstance(owner, types.ModuleType) and e2 is not None:

                md = e2["mod"].get(owner.__name__, {})
                for name, sid in md.items():
                    if None in keys or name in keys or name in ("__dict__", "__getattr__"):
                        readers |= {e2["tests"][i] for i in e2["sets"][sid]} & later
            groups.append({"mutator": rel, "owner": _owner_name(owner), "attr": attr, "spans": spans,
                           "keys": sorted(k for k in keys if k is not None) if None not in keys else None,
                           "readers": sorted(readers)})
    with open(out_path, "w", encoding="utf-8") as fh:
        json.dump({"groups": groups}, fh, sort_keys=True)
    for g in groups:
        print(f"order-state: {g['mutator']} mutates {g['owner']}.{g['attr']}{g['keys'] or ''}: "
              f"{sum(len(v) for v in g['spans'].values())} reach spans in {len(g['spans'])} files, "
              f"{len(g['readers'])} readers")


if __name__ == "__main__":
    if sys.argv[1:2] == ["build"] and len(sys.argv) in (5, 6):
        build(*sys.argv[2:])
    else:
        sys.exit(__doc__)
