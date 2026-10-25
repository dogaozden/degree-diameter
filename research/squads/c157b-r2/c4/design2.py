#!/usr/bin/env python3
"""design2.py (c4): local-search completion of a design_cover.py set. Chosen elements have pairwise disjoint cells
(mode L: elements = lines, cells = points; mode P: elements = points, cells = lines). Every needed cell that is not
already covered by a FIXED element (fixed elements of the kind chosen here, whose cells are covered by other sets)
must be covered by a chosen element. Move: for an uncovered needed cell x, try each element e through x, remove the
chosen elements that share a cell with e (blockers), add e. Accept if the number of covered needed cells does not
drop; with probability PLATEAU also when it drops by one. Finally complete to a maximal set at random (as design_cover).
usage: design2.py HEXBIN L|P NEEDED.txt FIXED.txt|- INIT.txt|- SEED ITERS OUT.txt"""
import sys, os, numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import tm3_build as T
hexfn, mode, needf, fixf, initf, seed, iters, out = sys.argv[1:9]
seed = int(seed); iters = int(iters); PLATEAU = 0.2
q, N, LP, PL, fp, fl = T.load_hex(hexfn)
rng = np.random.default_rng(seed)
EC, CAND = (LP, PL) if mode == 'L' else (PL, LP)   # EC[e]: cells of element e; CAND[c]: elements through cell c
ld = lambda f: np.loadtxt(f, dtype=np.int64).reshape(-1)
need = np.unique(ld(needf))
isneed = np.zeros(N, bool); isneed[need] = True
pre = np.zeros(N, bool)                             # cells already covered by the fixed elements
if fixf != '-':
    fx = ld(fixf)
    if len(fx): pre[EC[fx].reshape(-1)] = True
need_m = isneed & ~pre
owner = -np.ones(N, np.int64); chosen = set()
def add(e): chosen.add(int(e)); owner[EC[e]] = e
def rem(e): chosen.discard(int(e)); owner[EC[e]] = -1
init = ld(initf) if initf != '-' else np.zeros(0, np.int64)
for e in init:
    assert (owner[EC[e]] == -1).all(), 'init not a packing'
    add(e)
print(f'init {len(chosen)} elements; needed cells {int(need_m.sum())}; uncovered at start {int((need_m & (owner < 0)).sum())}', flush=True)
for it in range(iters):
    unc = np.nonzero(need_m & (owner < 0))[0]
    if len(unc) == 0: break
    for x in unc[rng.permutation(len(unc))]:
        if owner[x] >= 0: continue
        best, bestnet, bestB = None, -10**9, None
        for e in CAND[x]:
            B = set(int(owner[c]) for c in EC[e] if owner[c] >= 0)
            # net change of covered needed cells: + needed cells of e, - needed cells of the removed blockers
            net = int(need_m[EC[e]].sum()) - sum(int(need_m[EC[f]].sum()) for f in B) + rng.random() * 0.01
            if net > bestnet: best, bestnet, bestB = e, net, B
        if best is None: continue
        if bestnet >= 0 or (bestnet > -1.5 and rng.random() < PLATEAU):
            for f in bestB: rem(f)
            add(best)
print('after local search: chosen', len(chosen), 'uncovered needed', int((need_m & (owner < 0)).sum()), 'of', int(need_m.sum()), flush=True)
for e in rng.permutation(N):
    if (owner[EC[e]] < 0).all(): add(e)
ch = np.array(sorted(chosen), dtype=np.int64)
cnt = np.zeros(N, np.int64); np.add.at(cnt, EC[ch].reshape(-1), 1); assert cnt.max() <= 1
np.savetxt(out, ch, fmt='%d')
print(f'{mode}: {len(need)} needed, {int(need_m.sum())} need a chosen element, uncovered {int((need_m & (owner < 0)).sum())}; {len(ch)} elements -> {out}')
