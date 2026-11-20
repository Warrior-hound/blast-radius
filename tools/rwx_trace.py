"""pytest plugin: record, per test, which source lines run and which files are opened.

Load with `pytest -p rwx_trace`. Writes one JSON file per process to $RWX_TRACE_OUT:
  {"collect": {file: [lines]}, "tests": {nodeid: {"lines": {file: [lines]}, "opened": [paths]}}}
"collect" is everything executed while importing and collecting (module-level code, class bodies,
decorators): a change there can affect any test that imports the module.

Uses sys.monitoring (Python 3.12+): LINE events are disabled per location after their first hit and
re-armed with restart_events() at every test start, so each line costs one callback per test.
"""
import json
import os
import sys

import pytest

ROOT = os.path.realpath(os.environ.get("RWX_ROOT", os.getcwd())) + os.sep
TOOL = 4
mon = sys.monitoring
DISABLE = mon.DISABLE

_cur_lines = {}
_cur_open = set()
_collect_lines = {}
_tests = {}
_target = _collect_lines  # where LINE hits go right now


def _rel(path):
    if not path:
        return None
    try:
        p = os.path.realpath(path)
    except (OSError, ValueError):
        return None
    if not p.startswith(ROOT):
        return None
    return p[len(ROOT):].replace(os.sep, "/")


_relcache = {}


def _relfile(f):
    r = _relcache.get(f, 0)
    if r == 0:
        r = _rel(f)
        if r is not None and not (r.startswith("sqlglot/") or r.startswith("tests/") or r.startswith("sqlglotc/")):
            r = None
        _relcache[f] = r
    return r


def _line(code, line):
    r = _relfile(code.co_filename)
    if r is None:
        return DISABLE
    s = _target.get(r)
    if s is None:
        s = _target[r] = set()
    s.add(line)
    return DISABLE


_cur_classes = set()
_SELFLIKE = ("self", "cls", "mcs", "klass")


def _start(code, offset):
    """PY_START: record the class of the receiver of every sqlglot method call. A class-body change
    (e.g. a dialect constant read by shared code) affects tests that used that class, even when no
    line inside the class ran. Never disabled for methods, since receivers differ per call."""
    r = _relfile(code.co_filename)
    if r is None or not r.startswith("sqlglot/") or not code.co_varnames or code.co_varnames[0] not in _SELFLIKE or code.co_argcount == 0:
        return DISABLE
    try:
        v = sys._getframe(1).f_locals.get(code.co_varnames[0])
    except Exception:
        return None
    if v is None:
        return None
    _cur_classes.add(v if isinstance(v, type) else type(v))
    return None


def _audit(event, args):
    if event == "open" and args and isinstance(args[0], (str, bytes, os.PathLike)):
        try:
            r = _rel(os.fsdecode(args[0]))
        except Exception:
            r = None
        if r is not None:
            _cur_open.add(r)


import concurrent.futures as _cf
import pickle as _pickle


class _InProcessExecutor(_cf.Executor):
    """Stand-in for ProcessPoolExecutor while tracing: runs each task in this process so its lines
    are attributed to the current test, but keeps the pickle round-trip of the task, its arguments,
    the initializer's arguments and the result, because a real process pool exercises that code too."""

    def __init__(self, max_workers=None, mp_context=None, initializer=None, initargs=(), **kw):
        if initializer is not None:
            fn, args = _pickle.loads(_pickle.dumps((initializer, tuple(initargs))))
            fn(*args)

    def submit(self, fn, /, *args, **kwargs):
        fut = _cf.Future()
        try:
            f, a, k = _pickle.loads(_pickle.dumps((fn, args, kwargs)))
            fut.set_result(_pickle.loads(_pickle.dumps(f(*a, **k))))
        except BaseException as e:  # noqa: BLE001 - mirror the pool: the error goes to the future
            fut.set_exception(e)
        return fut

    def shutdown(self, wait=True, *, cancel_futures=False):
        pass


if os.environ.get("RWX_TRACE_INPROCESS", "1") == "1":
    _cf.ProcessPoolExecutor = _InProcessExecutor
    import concurrent.futures.process as _cfp
    _cfp.ProcessPoolExecutor = _InProcessExecutor

mon.use_tool_id(TOOL, "rwx_trace")
mon.register_callback(TOOL, mon.events.LINE, _line)
mon.register_callback(TOOL, mon.events.PY_START, _start)
mon.set_events(TOOL, mon.events.LINE | mon.events.PY_START)


def _class_names(classes):
    out = set()
    for c in classes:
        for k in getattr(c, "__mro__", ()):
            mod = getattr(k, "__module__", "") or ""
            if mod.startswith("sqlglot"):
                out.add(f"{mod}:{k.__qualname__}")
    return sorted(out)
sys.addaudithook(_audit)


@pytest.hookimpl(hookwrapper=True)
def pytest_runtest_protocol(item, nextitem):
    global _target, _cur_lines
    _cur_lines = {}
    _cur_open.clear()
    _cur_classes.clear()
    _target = _cur_lines
    mon.restart_events()
    yield
    _target = _collect_lines
    _tests[item.nodeid] = {
        "lines": {f: sorted(s) for f, s in _cur_lines.items()},
        "opened": sorted(_cur_open),
        "classes": _class_names(_cur_classes),
    }
    mon.restart_events()


def pytest_sessionfinish(session):
    out = os.environ.get("RWX_TRACE_OUT")
    if not out:
        return
    os.makedirs(out, exist_ok=True)
    wid = os.environ.get("PYTEST_XDIST_WORKER", "main")
    with open(os.path.join(out, f"trace-{wid}.json"), "w", encoding="utf-8") as fh:
        json.dump({"collect": {f: sorted(s) for f, s in _collect_lines.items()}, "tests": _tests}, fh)
