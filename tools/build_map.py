"""Merge per-worker trace files into the compact map the selector ships with.

  python solution/rwx/build_map.py artifacts/rwx/trace data/blast-radius/kit/x/sample/tests.json solution/rwx/app/map.json.gz

Map format (JSON, gzip):
  tests:    [test id, ...]                  index = position; numbers are resolved by id at runtime
  sets:     [[test index, ...], ...]        unique test sets (deduplicated)
  lines:    {file: {line: set index}}       tests that executed that line
  opened:   {file: set index}               tests that opened that (non-.py) file, e.g. fixtures
  collect:  {file: [lines]}                 lines executed at import/collection time
  classes:  {"module:Qualname": set index}  tests that called a method on an instance of that class
                                           (or a subclass: the trace stores each receiver's whole MRO)
  missing:  [test id, ...]                  tests in tests.json with no trace (treated as unknown)
"""
import glob
import gzip
import json
import os
import sys


def main(trace_dir, tests_json, out):
    tests = [t["id"] for t in json.load(open(tests_json, encoding="utf-8"))["tests"]]
    index = {t: i for i, t in enumerate(tests)}
    lines = {}
    opened = {}
    collect = {}
    classes = {}
    seen = set()
    for path in sorted(glob.glob(os.path.join(trace_dir, "trace-*.json"))):
        d = json.load(open(path, encoding="utf-8"))
        for f, ls in d["collect"].items():
            collect.setdefault(f, set()).update(ls)
        for nid, rec in d["tests"].items():
            i = index.get(nid)
            if i is None:
                continue
            seen.add(i)
            for f, ls in rec["lines"].items():
                m = lines.setdefault(f, {})
                for ln in ls:
                    m.setdefault(ln, set()).add(i)
            for c in rec.get("classes", []):
                classes.setdefault(c, set()).add(i)
            for f in rec["opened"]:
                if "__pycache__" in f or f.endswith(".pyc"):
                    continue
                opened.setdefault(f, set()).add(i)
    sets, set_id = [], {}

    def sid(s):
        k = tuple(sorted(s))
        if k not in set_id:
            set_id[k] = len(sets)
            sets.append(list(k))
        return set_id[k]

    out_lines = {f: {str(ln): sid(s) for ln, s in sorted(m.items())} for f, m in sorted(lines.items())}
    out_opened = {f: sid(s) for f, s in sorted(opened.items())}
    doc = {
        "tests": tests,
        "sets": sets,
        "lines": out_lines,
        "opened": out_opened,
        "collect": {f: sorted(s) for f, s in sorted(collect.items())},
        "classes": {c: sid(s) for c, s in sorted(classes.items())},
        "missing": [tests[i] for i in range(len(tests)) if i not in seen],
    }
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with gzip.open(out, "wt", encoding="utf-8", compresslevel=9) as fh:
        json.dump(doc, fh, separators=(",", ":"))
    print(f"tests={len(tests)} traced={len(seen)} missing={len(doc['missing'])} files={len(out_lines)} "
          f"unique_sets={len(sets)} opened_files={len(out_opened)} classes={len(classes)} size={os.path.getsize(out)/1e6:.2f}MB")


if __name__ == "__main__":
    main(*sys.argv[1:4])
