#!/usr/bin/env python3
"""addscan.py (job d7-family): exhaustive scan for ONE more extra point of a mirrored configuration
(research/cell147/mirror/README.md: base R pairwise opposite, extras X pairwise opposite and non-collinear with R, one
line L_j per extra, lines pairwise opposite and not in the spread S). A new pair (x, l) is feasible when x is
non-collinear with R + X and opposite to every extra, l is not in S, opposite to every L_j, and for every type t (the set
of extras at distance 4) the base points of type t split by d(x, .) = 4 / 6 fit into the usable spread lines of type t
split by d(l, .) = 4 / 6, where the spread line meeting l (and those meeting l) become unusable. The annealers sample a
few pairs per move; this tests all of them. Lines are hashed by their split on the zero-slack types (where the split
must be exact). Distances by BFS in the incidence graph (any q).
usage: addscan.py HEXBIN STATE.npz SPREAD.npy OUT.npy [MAXX]"""
import sys, os, numpy as np, collections, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
t0 = time.time()
H = Hex(sys.argv[1]); st = np.load(sys.argv[2]); S = np.load(sys.argv[3]).astype(np.int64); N = H.N; q = H.q
maxx = int(sys.argv[5]) if len(sys.argv) > 5 else 10 ** 9
R = st['R'].astype(np.int64); X = st['X'].astype(np.int64); L = st['L'].astype(np.int64); k = len(X)
LP, PL = H.lp.astype(np.int64), H.pl.astype(np.int64)
def pdist_from(p):           # point distances 0/2/4/6 from point p to all points
    d = np.full(N, 6, np.int8); d[p] = 0
    l1 = PL[p]; p2 = np.unique(LP[l1]); p2 = p2[p2 != p]; d[p2] = 2
    l3 = np.unique(PL[p2]); p4 = np.unique(LP[l3]); p4 = p4[d[p4] == 6]; d[p4] = 4
    return d
def ldist_from(l):           # line distances 0/2/4/6 from line l to all lines
    d = np.full(N, 6, np.int8); d[l] = 0
    p1 = LP[l]; l2 = np.unique(PL[p1]); l2 = l2[l2 != l]; d[l2] = 2
    p3 = np.unique(LP[l2]); l4 = np.unique(PL[p3]); l4 = l4[d[l4] == 6]; d[l4] = 4
    return d
dX = [pdist_from(int(x)) for x in X]; dL = [ldist_from(int(l)) for l in L]
inS = np.zeros(N, bool); inS[S] = True
# types of base points and spread lines
tR = np.zeros(len(R), np.int64); tS = np.zeros(len(S), np.int64); exS = np.zeros(len(S), bool)
for j in range(k):
    tR |= (dX[j][R] == 4).astype(np.int64) << j
    tS |= (dL[j][S] == 4).astype(np.int64) << j
    exS |= dL[j][S] == 2
types = np.unique(np.concatenate([tR, tS]))
tid = {int(t): i for i, t in enumerate(types)}; T = len(types)
tRi = np.array([tid[int(t)] for t in tR]); tSi = np.array([tid[int(t)] for t in tS])
cntR = np.bincount(tRi, minlength=T); usable = ~exS; cntS = np.bincount(tSi[usable], minlength=T)
slack = cntS - cntR
print(f'q={q} |R|={len(R)} k={k} types={T} deficit now {np.maximum(0, -slack).sum()} zero-slack types {(slack == 0).sum()}; {time.time()-t0:.0f}s', flush=True)
assert (slack >= 0).all()
# candidate points: not collinear with R + X (distance >= 4 to all), opposite to all extras
dmin = np.full(N, 6, np.int8)
for p in list(R) + list(X):
    l1 = PL[p]; p2 = np.unique(LP[l1]); dmin[p2] = np.minimum(dmin[p2], 2); dmin[p] = 0
okx = dmin >= 4
for j in range(k): okx &= dX[j] == 6
candx = np.nonzero(okx)[0][:maxx]
# candidate lines: not in S, opposite to every L_j
okl = ~inS
for j in range(k): okl &= dL[j] == 6
candl = np.nonzero(okl)[0]
print(f'candidate points {len(candx)}, candidate lines {len(candl)}; {time.time()-t0:.0f}s', flush=True)
# split vectors of the lines: per type, usable spread lines at distance 4 (have1) and the unusable ones (meeting l)
Sidx = -np.ones(N, np.int64); Sidx[S] = np.arange(len(S))
zero = np.nonzero(slack == 0)[0]
table = collections.defaultdict(list); nl_ok = 0
for l in candl:
    p1 = LP[l]; l2 = np.unique(PL[p1]); l2 = l2[l2 != l]
    p3 = np.unique(LP[l2]); l4 = np.unique(PL[p3])
    s2 = Sidx[l2]; s2 = s2[s2 >= 0]; s2 = s2[usable[s2]]          # usable spread lines meeting l (become unusable)
    s4 = Sidx[l4]; s4 = s4[s4 >= 0]; s4 = s4[usable[s4]]
    s4 = np.setdiff1d(s4, s2)
    lost = np.bincount(tSi[s2], minlength=T)
    if (lost > slack).any(): continue
    h1 = np.bincount(tSi[s4], minlength=T)
    nl_ok += 1
    table[tuple(h1[zero].tolist())].append((int(l), h1, lost))
print(f'lines with no forced loss {nl_ok}, distinct zero-slack splits {len(table)}; {time.time()-t0:.0f}s', flush=True)
feas = []
for i, x in enumerate(candx):
    d = pdist_from(int(x))
    need1 = np.bincount(tRi[d[R] == 4], minlength=T)
    key = tuple(need1[zero].tolist())
    for (l, h1, lost) in table.get(key, ()):
        h0 = cntS - h1 - lost
        if (need1 <= h1).all() and ((cntR - need1) <= h0).all():
            feas.append((int(x), l))
    if i % 5000 == 0: print(f'  {i}/{len(candx)} points, {len(feas)} feasible; {time.time()-t0:.0f}s', flush=True)
print(f'FEASIBLE additions: {len(feas)}', flush=True)
np.save(sys.argv[4], np.array(feas, dtype=np.int64).reshape(-1, 2))
