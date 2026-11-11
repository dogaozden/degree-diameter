#!/usr/bin/env python3
"""climb.py m k r d SECONDS SEED START OUT: 1-element random-replacement plateau climb, Sidon constraint kept, D=10.
START is a solution file written by sidon_search.py (lines 'idx meta(a=A,j=J) z=0')."""
import sys, time, re
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/raise10/r2/e14')
from anatlib import Gp, reach
m, k, r, d, SECS, SEED = map(int, sys.argv[1:7]); START, OUT = sys.argv[7], sys.argv[8]; D = 10
rng = np.random.default_rng(SEED); Gr = Gp(m, k, r)
L = open(START).read().split('\n')
S = [tuple(map(int, re.search(r'a=(\d+),j=(\d+)', l).groups())) for l in L[1:1 + d]]
def ok(S):
    js = [s[1] for s in S]
    diffs = [(js[x] - js[y]) % k for x in range(d) for y in range(d) if x != y]
    return len(set(diffs)) == len(diffs) and 0 not in diffs and len(set(js)) == d and len(set(S)) == d
def cost(S): return max(int(np.sum(reach(Gr, S, side, D) < 0)) for side in (0, 1))
cur = cost(S); best = cur; t0 = time.time(); it = 0; acc = 0
def fmt(S, c):
    lines = [f"{d} {D} meta {m} {k} {r} n 1 N {m*k} cost {c}"]
    for a, j in S: lines.append(f"{a*k+j} meta(a={a},j={j}) z=0")
    return "\n".join(lines) + "\n"
while time.time() - t0 < SECS:
    it += 1
    i = int(rng.integers(1, d)); cand = list(S)
    a = int(rng.integers(m)); j = int(rng.integers(k))
    cand[i] = (a, j)
    if (a, j) == (0, 0) or not ok(cand): continue
    c = cost(cand)
    if c <= cur:
        if c < cur: acc += 1
        S, cur = cand, c
        if cur < best:
            best = cur; open(OUT, 'w').write(fmt(S, best))
        if cur == 0: break
print(f"climb: iters={it} best cost={best} final S={S} time={time.time()-t0:.0f}s")
