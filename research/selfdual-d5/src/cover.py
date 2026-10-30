#!/usr/bin/env python3
"""cover.py: coverage table of a sweep: per order, groups listed / searched (rc 0) / with a capped type / GAP or
timeout failures, the smallest near-miss value |G \\ XX| (NEAR targets) and the groups with solutions.
usage: cover.py GROUPLIST SWEEP.txt [SWEEP2.txt ...]   (GROUPLIST lines: N ID ncls ninv)"""
import sys, collections
listed = collections.defaultdict(set)
for l in open(sys.argv[1]):
    t = l.split()
    if len(t) >= 2: listed[int(t[0])].add(int(t[1]))
res = {}
for p in sys.argv[2:]:
    for l in open(p):
        t = l.split()
        if len(t) < 3 or not t[0].isdigit(): continue
        k = (int(t[0]), int(t[1]))
        if "GAPFAIL" in t: res.setdefault(k, ("gapfail",)); continue
        d = dict(zip(t[2::2], t[3::2]))
        res[k] = ("ok" if d.get("rc") == "0" else "rc" + d.get("rc", "?"), int(d.get("capped", 0)), int(d.get("sols", 0)), int(d.get("best", 1 << 40)) if d.get("best", "NA") != "NA" else 1 << 40)
print("| order | vertices | groups | searched | with a capped type | failed | best near miss | groups with solutions |")
print("|---:|---:|---:|---:|---:|---:|---:|---|")
tot = [0, 0, 0, 0]
for n in sorted(listed):
    ids = listed[n]; r = [res[(n, i)] for i in ids if (n, i) in res]
    ok = [x for x in r if x[0] == "ok"]; fail = len(r) - len(ok)
    cap = sum(1 for x in ok if x[1]); hits = sorted(i for i in ids if (n, i) in res and res[(n, i)][0] == "ok" and res[(n, i)][2])
    best = min((x[3] for x in ok), default=None)
    if not r: continue
    tot[0] += len(ids); tot[1] += len(ok); tot[2] += cap; tot[3] += fail
    bs = "-" if best is None or best >= 1 << 40 else str(best)
    print(f"| {n} | {2 * n} | {len(ids)} | {len(ok)} | {cap} | {fail} | {bs} | {', '.join(f'{n}_{i}' for i in hits) or '-'} |")
print(f"\ntotal listed (orders touched) {tot[0]}, searched {tot[1]}, with a capped type {tot[2]}, failed {tot[3]}")
