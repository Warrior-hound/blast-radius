# Blast Radius selector

For each sqlglot patch, pick the tests that can catch it and split them over at most 8 workers.

## How it decides
1. **Rebuild the changed files** in memory from the unified diff, against sqlglot at the pinned commit
   (fetched from sqlglot's own repository at `eb11aec` during the build).
2. **Null-change check:** compile the old and new module. If every code object is identical apart from
   line numbers, the change cannot alter behavior (comments, formatting), so it needs no tests.
3. **Exposure map** (`map.json.gz`, built once from the pinned commit with `tools/rwx_trace.py`):
   for every test, the source lines it executed, the files it opened (fixtures), and the classes it
   called methods on. A changed function selects the tests that executed it. A changed class body or
   module-level statement also selects every test that used that class or module.
4. **Import check:** when import-time code changed, the patched modules are imported in a throwaway
   interpreter; a crash there selects every test that imports them.
5. **Compile-stage cutoff for the TPC executor tests** (`e1_cutoff.py`, `e1map.json.gz`): when a changed
   function runs only while the TPC-H/TPC-DS queries are parsed, optimized and planned, the patched modules
   recompute those compile outputs in a throwaway interpreter; if every fingerprint matches the pinned one,
   the executor never sees a difference and those tests are not selected. Any mismatch, error or budget
   overrun keeps them.
6. **Fallbacks:** test configuration, unparseable or non-applying patches, and deleted modules widen
   the selection instead of guessing. Further guards widen it for change kinds the map cannot see:
   sources are compiled from bytes (PEP 263 encoding cookies), changed module-level names select the
   tests of modules that read them, a new file selects the tests that opened its directory or siblings,
   import-time functions of lazily imported modules select that module's users, import probes load unittest first (as the test run does), non-Python files in a
   test-named directory select those tests, and a probe timeout, crash or deadline skip selects every test.
7. **Operator-swap witness:** when a changed file's only edits are swapped comparison or boolean operators at sites traced on the pinned suite, and no evaluation anywhere in the suite would have produced a different value, the file adds no line-coverage tests (all guards still apply).
8. **Packing:** longest test first onto the least-loaded worker, with the worker count chosen to minimize
   the busiest worker's time plus 2 s per worker.

No table from patches or edit kinds to tests is used anywhere: the selection is computed from the patch
and the map of the pinned commit.

## Rebuilding the map
`tools/rwx_trace.py` is a pytest plugin (`pytest -p rwx_trace -n 8 tests`, with `RWX_TRACE_OUT` set)
run in the same base image; `tools/build_map.py` merges its output into `map.json.gz`.

## Reused code
- [sqlglot](https://github.com/tobymao/sqlglot) (MIT), source at commit eb11aec, downloaded at build time.

## License
MIT
