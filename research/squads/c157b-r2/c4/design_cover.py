#!/usr/bin/env python3
"""design_cover.py: a non-concurrent line set (mode L) containing a line through every needed point, or a non-collinear
point set (mode P) containing a point on every needed line, as far as possible; completed greedily (first from a given
base set, then at random) to a maximal set. Used for the non-bottleneck friendly sets of the relaxed (15,7) construction,
so that every paired element's partner is covered at the levels where its hubs must be wired (RELAXED.md).
usage: design_cover.py HEXBIN L|P NEEDED.txt BASE.txt SEED OUT.txt
  L: NEEDED = point ids, OUT = line ids (no two lines meet); P: NEEDED = line ids, OUT = point ids (no two collinear)"""
import sys, numpy as np
hexfn, mode, needf, basef, seed, out = sys.argv[1:7]
b = open(hexfn, 'rb').read()
q, N, Lc = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32)); Q1 = q + 1
LP = np.frombuffer(b[12:12 + 4 * Lc * Q1], dtype=np.int32).reshape(Lc, Q1).astype(np.int64)
flat_p = LP.reshape(-1); flat_l = np.repeat(np.arange(Lc), Q1)
PL = flat_l[np.lexsort((flat_l, flat_p))].reshape(N, Q1)
# mode L: elements = lines, their cells = points (LP); needed = points, candidates through a point = PL[x]
EC, CAND = (LP, PL) if mode == 'L' else (PL, LP)
rng = np.random.default_rng(int(seed))
need = np.unique(np.loadtxt(needf, dtype=np.int64).reshape(-1))
isneed = np.zeros(N, bool); isneed[need] = True
used = np.zeros(N, bool)          # cells (points in mode L) already covered by a chosen element
chosen = []
covered = np.zeros(N, bool)
for x in need[rng.permutation(len(need))]:
    if used[x]: continue          # some chosen element already passes through x
    cands = [e for e in CAND[x] if not used[EC[e]].any()]
    if not cands: continue
    # prefer the element covering the fewest other needed cells (capacity), ties at random
    k = np.array([isneed[EC[e]].sum() for e in cands]); best = [e for e, kk in zip(cands, k) if kk == k.min()]
    e = best[rng.integers(len(best))]
    chosen.append(e); used[EC[e]] = True
ncov = used[need].sum()
base = np.loadtxt(basef, dtype=np.int64).reshape(-1)
for e in base[rng.permutation(len(base))]:
    if not used[EC[e]].any(): chosen.append(e); used[EC[e]] = True
nb = len(chosen)
for e in rng.permutation(N):
    if not used[EC[e]].any(): chosen.append(e); used[EC[e]] = True
chosen = np.array(sorted(set(chosen)), dtype=np.int64)
assert len(chosen) == len(set(chosen.tolist()))
cnt = np.zeros(N, np.int64); np.add.at(cnt, EC[chosen].reshape(-1), 1); assert cnt.max() <= 1
np.savetxt(out, chosen, fmt='%d')
print(f'{mode}: {len(need)} needed, {ncov} covered; {len(chosen)} elements (after base {nb})')
