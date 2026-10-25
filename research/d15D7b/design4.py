#!/usr/bin/env python3
"""design4.py: design3.py (private covers) for a provider set that serves two roles: its A-slots (source level) cover
the needs NEED_A and its B-slots (target level) cover NEED_B. A chosen element may hold at most one needed cell of each
role (one A-demand and one B-demand use different slots, so they do not compete), and every needed cell of each role
gets a covering element. Chosen elements have pairwise disjoint cells.
usage: design4.py HEXBIN L|P NEED_A.txt|- NEED_B.txt|- INIT.txt SEED ITERS OUT.txt"""
import sys, os, numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import tm3_build as T
hexfn, mode, nAf, nBf, initf, seed, iters, out = sys.argv[1:9]
seed = int(seed); iters = int(iters); PLATEAU = 0.2
q, N, LP, PL, fp, fl = T.load_hex(hexfn)
rng = np.random.default_rng(seed)
EC, CAND = (LP, PL) if mode == 'L' else (PL, LP)
ld = lambda f: np.unique(np.loadtxt(f, dtype=np.int64).reshape(-1)) if f != '-' else np.zeros(0, np.int64)
needA, needB = ld(nAf), ld(nBf)
isA = np.zeros(N, bool); isA[needA] = True; isB = np.zeros(N, bool); isB[needB] = True
ncA = isA[EC].sum(1); ncB = isB[EC].sum(1)
owner = -np.ones(N, np.int64); chosen = set()
def add(e): chosen.add(int(e)); owner[EC[e]] = e
def rem(e): chosen.discard(int(e)); owner[EC[e]] = -1
for e in ld(initf):
    if ncA[e] <= 1 and ncB[e] <= 1 and (owner[EC[e]] < 0).all(): add(e)
def unc(): return np.nonzero((isA | isB) & (owner < 0))[0]
print(f'init kept {len(chosen)}; needed A {len(needA)} B {len(needB)}; uncovered {len(unc())}', flush=True)
for it in range(iters):
    U = unc()
    if len(U) == 0: break
    for x in U[rng.permutation(len(U))]:
        if owner[x] >= 0: continue
        best, bestnet, bestB = None, -10**9, None
        for e in CAND[x]:
            if ncA[e] > 1 or ncB[e] > 1: continue
            Bk = set(int(owner[c]) for c in EC[e] if owner[c] >= 0)
            # cells of e that are needed and would become covered, minus needed cells the removed blockers covered
            gain = int(((isA[EC[e]] | isB[EC[e]]) & (owner[EC[e]] < 0)).sum())
            loss = sum(int(((isA[EC[f]] | isB[EC[f]])).sum()) for f in Bk)
            net = gain - loss + rng.random() * 0.01
            if net > bestnet: best, bestnet, bestB = e, net, Bk
        if best is None: continue
        if bestnet >= 0 or (bestnet > -1.5 and rng.random() < PLATEAU):
            for f in bestB: rem(f)
            add(best)
print('after local search: chosen', len(chosen), 'uncovered', len(unc()), flush=True)
for e in rng.permutation(N):
    if ncA[e] == 0 and ncB[e] == 0 and (owner[EC[e]] < 0).all(): add(e)
ch = np.array(sorted(chosen), dtype=np.int64)
cnt = np.zeros(N, np.int64); np.add.at(cnt, EC[ch].reshape(-1), 1); assert cnt.max() <= 1
assert (ncA[ch] <= 1).all() and (ncB[ch] <= 1).all()
np.savetxt(out, ch, fmt='%d')
print(f'{mode}: needed A {len(needA)} B {len(needB)}, uncovered {len(unc())}; {len(ch)} elements -> {out}')
