#!/usr/bin/env python3
"""sidon_search.py m k r d SECONDS SEED OUT: random S under the Sidon-type j-projection constraint (D=10),
keep the lowest-cost S (cost = max over sides of unreached vertices). Writes the best S in solution format to OUT."""
import sys, time, math
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/raise10/r2/e14')
from anatlib import Gp, reach
m, k, r, d, SECS, SEED = map(int, sys.argv[1:7]); OUT = sys.argv[7]; D = 10
rng = np.random.default_rng(SEED); Gr = Gp(m, k, r)
best = (10**9, None); t0 = time.time(); n = 0
def fmt(S, cost):
    lines = [f"{d} {D} meta {m} {k} {r} n 1 N {m*k} cost {cost}"]
    for a, j in S: lines.append(f"{a*k+j} meta(a={a},j={j}) z=0")
    return "\n".join(lines) + "\n"
while time.time() - t0 < SECS:
    els = set()
    while len(els) < d - 1:
        a = int(rng.integers(m)); j = int(rng.integers(k))
        if (a, j) != (0, 0): els.add((a, j))
    S = [(0, 0)] + sorted(els)
    js = [s[1] for s in S]
    diffs = [(js[x] - js[y]) % k for x in range(d) for y in range(d) if x != y]
    if len(set(diffs)) != len(diffs) or 0 in diffs or len(set(js)) < d: continue
    n += 1
    cost = max(int(np.sum(reach(Gr, S, side, D) < 0)) for side in (0, 1))
    if cost < best[0]:
        best = (cost, S); open(OUT, 'w').write(fmt(S, cost))
print(f"m={m} k={k} r={r} d={d} sidon samples={n} best cost={best[0]} S={best[1]} time={time.time()-t0:.0f}s")
