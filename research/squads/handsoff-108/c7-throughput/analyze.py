#!/usr/bin/env python3
"""c7-throughput analysis. Parses IM lines (haar_c7 with IMLOG=1) and replays stop rules exactly.

A chain's trajectory up to its stop does not depend on REHEAT (REHEAT only decides when a chain stops; the schedule
restarts at each chain start), so a stall rule with REHEAT=r <= the recorded 30 s, and a chain-abort rule
"stop at chain time t if chain min > thr", can be replayed on the recorded improvement events without new runs.
usage: analyze.py LABEL=log.log [LABEL=log.log ...] [--policies ...]
"""
import re, sys

IM_RE = re.compile(r"^IM (\d+) end ([\d.]+) min (-?\d+) ev (\d+) ab (\d) n (\d+)(.*)$")

def parse(path):
    chains = []
    for line in open(path, errors="replace"):
        m = IM_RE.match(line.strip())
        if not m:
            continue
        pairs = [tuple(p.split(":")) for p in m.group(7).split()]
        ev = [(float(t), int(float(e))) for t, e in pairs]
        chains.append(dict(n=int(m.group(1)), end=float(m.group(2)), min=int(m.group(3)), ev=int(m.group(4)),
                           ab=int(m.group(5)), ev_t=[t for t, _ in ev], ev_e=[e for _, e in ev]))
    return chains

def lbest_at(ch, t):
    """chain minimum at chain time t (last event with time <= t)."""
    val = None
    for tt, ee in zip(ch["ev_t"], ch["ev_e"]):
        if tt <= t + 1e-9:
            val = ee
        else:
            break
    return val

def replay(ch, reheat=30.0, aborts=()):
    """return (stop_time, min_at_stop, how) under stall rule REHEAT=reheat (<=30) and abort list [(t, thr)]."""
    ts, es = ch["ev_t"], ch["ev_e"]
    n = len(ts)
    stall_t, stall_min = None, None
    for k in range(n):
        last = (k == n - 1)
        if last:
            stop = ts[k] + reheat
            stall_t, stall_min = stop, es[k]
            break
        if ts[k + 1] - ts[k] > reheat:
            stall_t, stall_min = ts[k] + reheat, es[k]
            break
    # recorded chain (REHEAT=30): stall_t from the same rule with reheat=30 must equal ch["end"]
    ab_t = None
    for t, thr in sorted(aborts):
        if t >= stall_t:
            break
        v = lbest_at(ch, t)
        if v is not None and v > thr:
            ab_t = t
            break
    if ab_t is not None:
        return ab_t, lbest_at(ch, ab_t), "abort"
    return stall_t, stall_min, "stall"

def summarize(chains, reheat=30.0, aborts=()):
    stops = [replay(c, reheat, aborts) for c in chains]
    total = sum(s[0] for s in stops)
    mins = [s[1] for s in stops]
    res = dict(n=len(stops), hours=total / 3600.0, med=sorted(mins)[len(mins) // 2] if mins else None)
    for X in (9, 12, 15):
        c = sum(1 for m in mins if m <= X)
        res[f"le{X}"] = c
        res[f"r{X}"] = c / (total / 3600.0) if total > 0 else 0.0
    res["aborted"] = sum(1 for s in stops if s[2] == "abort")
    return res

def main(argv):
    runs = []
    for a in argv:
        if "=" not in a:
            continue
        lab, path = a.split("=", 1)
        runs.append((lab, parse(path)))
    # self-check: the recorded stall rule must reproduce the logged chain end and min (REHEAT=30)
    bad = 0
    for lab, chs in runs:
        for c in chs:
            s = replay(c, 30.0, ())
            if abs(s[0] - c["end"]) > 0.06 or s[1] != c["min"]:
                bad += 1
    print(f"# self-check mismatches (REHEAT=30 replay vs logged end/min): {bad}")
    print("| run | policy | chains | CPU h | min<=12 | min<=9 | rate<=12 /CPU-h | rate<=9 /CPU-h | median min | aborted |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    policies = [("REHEAT 30 (as run)", 30.0, ())]
    for r in (20.0, 15.0, 10.0, 5.0):
        policies.append((f"REHEAT {r:g}", r, ()))
    for lab, chs in runs:
        for name, r, ab in policies:
            s = summarize(chs, r, ab)
            print(f"| {lab} | {name} | {s['n']} | {s['hours']:.3f} | {s['le12']} | {s['le9']} | {s['r12']:.1f} | {s['r9']:.2f} | {s['med']} | {s['aborted']} |")
    if "--dump" in sys.argv:
        for lab, chs in runs:
            for c in chs:
                pts = [lbest_at(c, t) for t in (5, 10, 15, 20, 25, 30)]
                print(lab, c["n"], "end=%.1f" % c["end"], "min", c["min"], "lbest@5..30", pts)

if __name__ == "__main__":
    main(sys.argv[1:])
