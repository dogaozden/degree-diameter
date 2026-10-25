#!/usr/bin/env python3
"""design3.py (squad c157b-r2 card c4): private-cover design for a non-bottleneck friendly set. Every needed cell (a paired element of a
bottleneck set) gets its own chosen covering element, and each chosen element contains at most ONE needed cell.
Why: a demand (r with partner x) can only use a slot of an element through x; if a chosen element contains two needed
cells (or the joining line of a pair, which contains both ends), two demands compete for one slot and one pair fails.
Chosen elements have pairwise disjoint cells (mode L: lines, cells = points; mode P: points, cells = lines).
Starts from INIT (design_cover output, keeping only its elements with <= 1 needed cell), covers the rest by local search
(an uncovered needed x takes a candidate element e through x that contains no other needed cell, removing its blockers),
then completes at random with elements containing no needed cell.
usage: design3.py HEXBIN L|P NEEDED.txt INIT.txt|- SEED ITERS OUT.txt"""
import sys, os, numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import tm3_build as T
hexfn, mode, needf, initf, seed, iters, out = sys.argv[1:8]
seed = int(seed); iters = int(iters); PLATEAU = 0.2
q, N, LP, PL, fp, fl = T.load_hex(hexfn)
rng = np.random.default_rng(seed)
EC, CAND = (LP, PL) if mode == 'L' else (PL, LP)   # EC[e]: cells of element e; CAND[c]: elements through cell c
ld = lambda f: np.loadtxt(f, dtype=np.int64).reshape(-1)
need = np.unique(ld(needf))
isneed = np.zeros(N, bool); isneed[need] = True
nc = isneed[EC].sum(1)                              # needed cells on each element
owner = -np.ones(N, np.int64); chosen = set()
def add(e): chosen.add(int(e)); owner[EC[e]] = e
def rem(e): chosen.discard(int(e)); owner[EC[e]] = -1
init = ld(initf) if initf != '-' else np.zeros(0, np.int64)
for e in init:
    if nc[e] <= 1 and (owner[EC[e]] < 0).all(): add(e)
print(f'init kept {len(chosen)} elements; needed cells {len(need)}; uncovered {int((isneed & (owner < 0)).sum())}', flush=True)
for it in range(iters):
    unc = np.nonzero(isneed & (owner < 0))[0]
    if len(unc) == 0: break
    for x in unc[rng.permutation(len(unc))]:
        if owner[x] >= 0: continue
        best, bestnet, bestB = None, -10**9, None
        for e in CAND[x]:
            if nc[e] != 1: continue                 # only x may be needed on e
            B = set(int(owner[c]) for c in EC[e] if owner[c] >= 0)
            net = 1 - sum(int(nc[f]) for f in B) + rng.random() * 0.01
            if net > bestnet: best, bestnet, bestB = e, net, B
        if best is None: continue
        if bestnet >= 0 or (bestnet > -1.5 and rng.random() < PLATEAU):
            for f in bestB: rem(f)
            add(best)
print('after local search: chosen', len(chosen), 'uncovered needed', int((isneed & (owner < 0)).sum()), flush=True)
for e in rng.permutation(N):
    if nc[e] == 0 and (owner[EC[e]] < 0).all(): add(e)
ch = np.array(sorted(chosen), dtype=np.int64)
cnt = np.zeros(N, np.int64); np.add.at(cnt, EC[ch].reshape(-1), 1); assert cnt.max() <= 1
assert (nc[ch] <= 1).all()
np.savetxt(out, ch, fmt='%d')
print(f'{mode}: {len(need)} needed, uncovered {int((isneed & (owner < 0)).sum())}, max needed per element {int(nc[ch].max())}; {len(ch)} elements -> {out}')
