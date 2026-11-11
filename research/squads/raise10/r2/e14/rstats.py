#!/usr/bin/env python3
"""rstats.py m k r SAMPLES SEED MODE: random S = {e} + (d-1) random non-identity elements, D=10, d=4.
d given as argv[6]. MODE 'any': uniform random; MODE 'jgen': j-projection of S must be distinct and generate Z_k.
Prints: cost distribution (max over sides of unreached count), holes per j-order class, rate per class."""
import sys, math
import numpy as np
from collections import Counter
sys.path.insert(0, '/home/user/degree-diameter/research/squads/raise10/r2/e14')
from anatlib import Gp, reach
m, k, r, SAMP, SEED, d = map(int, sys.argv[1:7]); MODE = sys.argv[7]; D = 10
rng = np.random.default_rng(SEED)
Gr = Gp(m, k, r); N = Gr.N
def ordk(j): return k // math.gcd(j, k) if j % k else 1
classes = Counter(ordk(j) for j in range(k) for a in range(m))  # element counts per class
cls_count = Counter()
for j in range(k):
    cls_count[ordk(j)] += m
costs = []; holes_by_cls = Counter(); samp_with_hole = 0; tot_holes = 0
def gcd_gen(js):
    g = k
    for j in js: g = math.gcd(g, j % k)
    return g
done = 0; tries = 0
while done < SAMP:
    tries += 1
    els = set()
    while len(els) < d - 1:
        a = int(rng.integers(m)); j = int(rng.integers(k))
        if (a, j) != (0, 0): els.add((a, j))
    S = [(0, 0)] + sorted(els)
    if MODE == 'sidon':
        js = [s[1] for s in S]
        diffs = [(js[x] - js[y]) % k for x in range(d) for y in range(d) if x != y]
        if len(set(diffs)) != len(diffs) or 0 in diffs or len(set(js)) < d: continue
    if MODE == 'jgen':
        js = [0] + [s[1] for s in S[1:]]
        if len(set(js)) < d or gcd_gen(js) != 1: continue
    done += 1
    worst = 0; hs = []
    for side in (0, 1):
        dist = reach(Gr, S, side, D)   # target-side distances, -1 unreached
        unr = np.nonzero(dist < 0)[0]
        worst = max(worst, len(unr))
        for h in unr:
            j = int(h) % k
            hs.append(ordk(j))
    costs.append(worst)
    tot_holes += len(hs)
    holes_by_cls.update(hs)
print(f"group Z_{m} x| Z_{k} r={r} mode={MODE} samples={SAMP} tries={tries}")
print("cost (max unreached over sides) distribution:", dict(sorted(Counter(costs).items())))
print("solved (cost 0) fraction:", sum(1 for c in costs if c == 0) / len(costs))
ov = tot_holes / (2 * N * SAMP)
print(f"overall hole rate per vertex per side: {ov:.3e}")
for c in sorted(cls_count):
    rate = holes_by_cls[c] / (2 * cls_count[c] * SAMP) if cls_count[c] else 0
    print(f"  j-order {c}: elements {cls_count[c]}, holes {holes_by_cls[c]}, rate {rate:.3e}, ratio to overall {rate/ov if ov else 0:.2f}")
