#!/usr/bin/env python3
"""swapscan.py (job d7-family): exhaustive 1-out / 2-in moves for a mirrored configuration (see addscan.py): for every
extra point j, remove (x_j, L_j), list ALL feasible single additions (addscan's test), then test every pair of them
for joint feasibility (points opposite, lines opposite, and the type condition with both added). A feasible pair gives
k + 1 extra points. Writes the first improved state found (np.savez R, X, L) and stops, or reports none.
With MODE=base (env), the removed element is a base point instead (net +1 again when two additions fit).
usage: swapscan.py HEXBIN STATE.npz SPREAD.npy OUT.npz [J0 J1]   (only extras / base points J0 <= j < J1)"""
import sys, os, numpy as np, collections, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
t0 = time.time()
H = Hex(sys.argv[1]); st = np.load(sys.argv[2]); S = np.load(sys.argv[3]).astype(np.int64); N = H.N; q = H.q
R0 = st['R'].astype(np.int64); X0 = st['X'].astype(np.int64); L0 = st['L'].astype(np.int64); k0 = len(X0)
BASE = os.environ.get('MODE') == 'base'
J0, J1 = (int(sys.argv[5]), int(sys.argv[6])) if len(sys.argv) > 6 else (0, len(R0) if BASE else k0)
LP, PL = H.lp.astype(np.int64), H.pl.astype(np.int64)
inS = np.zeros(N, bool); inS[S] = True
Sidx = -np.ones(N, np.int64); Sidx[S] = np.arange(len(S))
_pd = {}; _ld = {}
def pdist_from(p):
    if p in _pd: return _pd[p]
    d = np.full(N, 6, np.int8); d[p] = 0
    p2 = np.unique(LP[PL[p]]); p2 = p2[p2 != p]; d[p2] = 2
    p4 = np.unique(LP[np.unique(PL[p2])]); p4 = p4[d[p4] == 6]; d[p4] = 4
    if len(_pd) < 20000: _pd[p] = d
    return d
def lsplit(l):
    """spread indices meeting l (dist 2) and at distance 4"""
    if l in _ld: return _ld[l]
    l2 = np.unique(PL[LP[l]]); l2 = l2[l2 != l]
    l4 = np.unique(PL[np.unique(LP[l2])])
    s2 = Sidx[l2]; s2 = s2[s2 >= 0]; s4 = Sidx[l4]; s4 = s4[s4 >= 0]; s4 = np.setdiff1d(s4, s2)
    o = (s2, s4, l2, l4)
    if len(_ld) < 200000: _ld[l] = o
    return o
def feasible(R, X, L, extra_pts=None):
    """all feasible single additions (x, l) to the configuration (R, X, L)"""
    k = len(X)
    dX = [pdist_from(int(x)) for x in X]
    tR = np.zeros(len(R), np.int64); tS = np.zeros(len(S), np.int64); exS = np.zeros(len(S), bool)
    for j in range(k):
        tR |= (dX[j][R] == 4).astype(np.int64) << j
        s2, s4, _, _ = lsplit(int(L[j])); exS[s2] = True
        b = np.zeros(len(S), np.int64); b[s4] = 1; tS |= b << j
    types = np.unique(np.concatenate([tR, tS])); T = len(types)
    tRi = np.searchsorted(types, tR); tSi = np.searchsorted(types, tS)
    usable = ~exS
    cntR = np.bincount(tRi, minlength=T); cntS = np.bincount(tSi[usable], minlength=T); slack = cntS - cntR
    if (slack < 0).any(): return None
    dmin = np.full(N, 6, np.int8)
    for p in list(R) + list(X):
        p2 = np.unique(LP[PL[p]]); dmin[p2] = np.minimum(dmin[p2], 2); dmin[p] = 0
    okx = dmin >= 4
    for j in range(k): okx &= dX[j] == 6
    candx = np.nonzero(okx)[0]
    Lset = set(int(l) for l in L)
    okl = ~inS
    for j in range(k):
        _, _, l2, l4 = lsplit(int(L[j]))
        okl[l2] = False; okl[l4] = False; okl[int(L[j])] = False
    candl = np.nonzero(okl)[0]
    zero = np.nonzero(slack == 0)[0]
    table = collections.defaultdict(list)
    for l in candl:
        s2, s4, _, _ = lsplit(int(l))
        s2u = s2[usable[s2]]; s4u = s4[usable[s4]]
        lost = np.bincount(tSi[s2u], minlength=T)
        if (lost > slack).any(): continue
        h1 = np.bincount(tSi[s4u], minlength=T)
        table[tuple(h1[zero].tolist())].append((int(l), h1, lost))
    out = []
    for x in candx:
        d = pdist_from(int(x))
        need1 = np.bincount(tRi[d[R] == 4], minlength=T)
        for (l, h1, lost) in table.get(tuple(need1[zero].tolist()), ()):
            if (need1 <= h1).all() and ((cntR - need1) <= cntS - h1 - lost).all(): out.append((int(x), l))
    return out
print(f'q={q} k={k0}', flush=True)
for j in range(J0, J1):
    if BASE: X, L, Rj = X0, L0, np.delete(R0, j)
    else: X, L, Rj = np.delete(X0, j), np.delete(L0, j), R0
    A = feasible(Rj, X, L)
    if A is None: continue
    if not BASE or len(A) >= 2 or j % 50 == 0: print(f'{"base" if BASE else "extra"} {j}: {len(A)} feasible single additions after removing it; {time.time()-t0:.0f}s', flush=True)
    if len(A) < 2: continue
    found = None
    for i, (xa, la) in enumerate(A):
        X2 = np.append(X, xa); L2 = np.append(L, la)
        # candidates for the second addition: the rest of A that are compatible with (xa, la)
        rest = [(xb, lb) for (xb, lb) in A[i + 1:] if pdist_from(xb)[xa] == 6 and lb not in set(np.concatenate(lsplit(la)[2:]).tolist()) and lb != la]
        if not rest: continue
        B = feasible(Rj, X2, L2)
        if B is None: continue
        Bs = set(B)
        hit = [p for p in rest if p in Bs]
        if hit: found = (X2, L2, hit[0]); break
    if found:
        X2, L2, (xb, lb) = found
        np.savez(sys.argv[4], R=Rj, X=np.append(X2, xb), L=np.append(L2, lb))
        print(f'IMPROVED: removed {"base point" if BASE else "extra"} {j}, added 2 -> |R\'| = {len(Rj) + len(X2) + 1}; wrote {sys.argv[4]}', flush=True)
        sys.exit(0)
print('no 1-out / 2-in improvement', flush=True)
