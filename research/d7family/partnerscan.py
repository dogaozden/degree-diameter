#!/usr/bin/env python3
"""partnerscan.py (job d7-family): probe3.py with addscan.py's hashing, for large q. Exhaustive test whether ONE
partner point can join a mirrored configuration: y collinear with exactly one base point a and with no other point of
R' = R + X, not collinear with any extra; M a line not in S meeting exactly one spread line s_M (which becomes sigma(a);
type of s_M = type of a) and no L_j, with d(M, L_j) = d(y, x_j) for all extras; for every type the base points other
than a at distance 4 / 6 from y fit into the usable spread lines other than s_M at distance 4 / 6 from M.
usage: partnerscan.py HEXBIN STATE.npz SPREAD.npy OUT.npy"""
import sys, os, numpy as np, collections, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
t0 = time.time()
H = Hex(sys.argv[1]); st = np.load(sys.argv[2]); S = np.load(sys.argv[3]).astype(np.int64); N = H.N; q = H.q
R = st['R'].astype(np.int64); X = st['X'].astype(np.int64); L = st['L'].astype(np.int64); k = len(X)
LP, PL = H.lp.astype(np.int64), H.pl.astype(np.int64)
def pdist_from(p):
    d = np.full(N, 6, np.int8); d[p] = 0
    p2 = np.unique(LP[PL[p]]); p2 = p2[p2 != p]; d[p2] = 2
    p4 = np.unique(LP[np.unique(PL[p2])]); p4 = p4[d[p4] == 6]; d[p4] = 4
    return d
def ldist_from(l):
    d = np.full(N, 6, np.int8); d[l] = 0
    l2 = np.unique(PL[LP[l]]); l2 = l2[l2 != l]; d[l2] = 2
    l4 = np.unique(PL[np.unique(LP[l2])]); l4 = l4[d[l4] == 6]; d[l4] = 4
    return d
dX = [pdist_from(int(x)) for x in X]; dL = [ldist_from(int(l)) for l in L]
inS = np.zeros(N, bool); inS[S] = True; Sidx = -np.ones(N, np.int64); Sidx[S] = np.arange(len(S))
tR = np.zeros(len(R), np.int64); tS = np.zeros(len(S), np.int64); exS = np.zeros(len(S), bool)
for j in range(k):
    tR |= (dX[j][R] == 4).astype(np.int64) << j; tS |= (dL[j][S] == 4).astype(np.int64) << j; exS |= dL[j][S] == 2
types = np.unique(np.concatenate([tR, tS])); T = len(types)
tRi = np.searchsorted(types, tR); tSi = np.searchsorted(types, tS); usable = ~exS
cntR = np.bincount(tRi, minlength=T); cntS = np.bincount(tSi[usable], minlength=T); slack = cntS - cntR
assert (slack >= 0).all()
zero = np.nonzero(slack == 0)[0]
print(f'q={q} |R|={len(R)} k={k} types={T} zero-slack {len(zero)}; {time.time()-t0:.0f}s', flush=True)
# lines M: not in S, meets no L_j, meets exactly one usable spread line s_M
okl = ~inS
for j in range(k): okl &= dL[j] != 2
okl[L] = False
table = collections.defaultdict(list); nM = 0
for M in np.nonzero(okl)[0]:
    l2 = np.unique(PL[LP[M]]); l2 = l2[l2 != M]
    s2 = Sidx[l2]; s2 = s2[s2 >= 0]
    if len(s2) != 1 or not usable[s2[0]]: continue
    sm = int(s2[0])
    l4 = np.unique(PL[np.unique(LP[l2])]); s4 = Sidx[l4]; s4 = s4[s4 >= 0]; s4 = s4[usable[s4]]; s4 = s4[s4 != sm]
    h1 = np.bincount(tSi[s4], minlength=T)
    dl = tuple(int(dL[j][M] == 4) for j in range(k))
    nM += 1
    table[(dl, int(tSi[sm]), tuple(h1[zero].tolist()))].append((int(M), sm, h1))
print(f'candidate lines {nM}, keys {len(table)}; {time.time()-t0:.0f}s', flush=True)
# partners y
collc = np.zeros(N, np.int64)
for p in list(R) + list(X):
    p2 = np.unique(LP[PL[p]]); p2 = p2[p2 != p]; collc[p2] += 1
inRp = np.zeros(N, bool); inRp[R] = True; inRp[X] = True
feas = []; ny = 0
for i, a in enumerate(R):
    p2 = np.unique(LP[PL[a]]); p2 = p2[p2 != a]
    for y in p2:
        if inRp[y] or collc[y] != 1: continue
        ny += 1
        d = pdist_from(int(y))
        dx = tuple(int(d[x] == 4) for x in X)
        if any(d[x] == 2 for x in X): continue
        m = d[R] == 4; m[i] = False
        need1 = np.bincount(tRi[m], minlength=T)
        for (M, sm, h1) in table.get((dx, int(tRi[i]), tuple(need1[zero].tolist())), ()):
            cR = cntR.copy(); cR[tRi[i]] -= 1; cS = cntS.copy(); cS[tSi[sm]] -= 1
            if (need1 <= h1).all() and ((cR - need1) <= (cS - h1)).all(): feas.append((int(a), int(y), M, int(S[sm])))
    if i % 100 == 0: print(f'  base {i}/{len(R)}, {ny} partners tried, {len(feas)} feasible; {time.time()-t0:.0f}s', flush=True)
print(f'FEASIBLE partners: {len(feas)} (of {ny} candidate y)', flush=True)
np.save(sys.argv[4], np.array(feas, dtype=np.int64).reshape(-1, 4))
