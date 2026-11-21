



import os, sys, time

_TICK = os.sysconf("SC_CLK_TCK") if hasattr(os, "sysconf") else 100
ACC, CNT, _STACK, CALLS = {}, {}, [], []
_ME = os.getpid()


def cpu_now():
    t = os.times()
    tot = t.user + t.system + t.children_user + t.children_system
    try:
        for p in os.listdir("/proc"):
            if not p.isdigit() or int(p) == _ME:
                continue
            try:
                with open(f"/proc/{p}/stat", "rb") as fh:
                    f = fh.read().rsplit(b")", 1)[1].split()
                tot += (int(f[11]) + int(f[12]) + int(f[13]) + int(f[14])) / _TICK
            except OSError:
                pass
    except OSError:
        pass
    return tot


def wrap(name, fn):
    def w(*a, **k):
        c0 = cpu_now()
        _STACK.append(0.0)
        try:
            return fn(*a, **k)
        finally:
            inner = _STACK.pop()
            d = cpu_now() - c0
            ACC[name] = ACC.get(name, 0.0) + d - inner
            CNT[name] = CNT.get(name, 0) + 1
            CALLS.append((name, d - inner))
            if _STACK:
                _STACK[-1] += d
    w.__wrapped__ = fn
    return w


def report(log, total):
    s = sum(ACC.values())
    for k, v in sorted(ACC.items(), key=lambda x: -x[1]):
        log(f"PROF {k:24s} {v:8.3f}s  n={CNT[k]}")
    log(f"PROF {'other(select etc)':24s} {total - s:8.3f}s")
    log(f"PROF {'TOTAL':24s} {total:8.3f}s")
