#!/usr/bin/env python3
"""Mirrored surgery set for the (2r+1)-copy hexagon graphs of research/d13D7/multi.c (DUALFILE mode).
R' = R756 (pairwise opposite points) + extra points X (non-collinear with everything, distance-4 pairs allowed),
L' = sigma(R'): lines, pairwise non-concurrent, with d(sigma(a), sigma(b)) = 4 exactly when d(a, b) = 4, and sigma a
local duality at every point of R' (midpoint of a distance-4 pair -> the connecting line of the image pair).
This file: one extra point x (k = 1).  Lines for R756: Hermitian spread lines (x0 + x4 = 0), chosen by type.
usage: mirror1.py SEED OUTDIR"""
import numpy as np, sys, random, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
seed = int(sys.argv[1]); out = sys.argv[2]; os.makedirs(out, exist_ok=True)
rng = random.Random(seed)
H = Hex(SP + 'hex_q11.bin'); N = H.N
R = np.load(SP + 'R756idx.npy').tolist(); S = np.load(SP + 'S_herm.npy').tolist(); Sset = set(S)
G2p = {p: None for p in []}
def coll(p): return H.collinear_points(p)          # Gamma_2 of a point (132 points)
def meet(l): return H.lines_meeting(l)            # Gamma_2 of a line (132 lines)
col = set()
for r in R: col |= coll(r)
Rset = set(R)
# choose x: non-collinear with R, smallest c(x)
cand = [p for p in range(N) if p not in col and p not in Rset]
Bm = H.Bmat(np.array(cand), np.array(R)); c = (Bm == 0).sum(axis=1)
best = [cand[i] for i in range(len(cand)) if c[i] == c.min()]
x = rng.choice(best)
Nx = [R[j] for j in np.nonzero(H.Bmat(np.array([x]), np.array(R))[0] == 0)[0]]
print('x =', x, 'c(x) =', len(Nx))
# check distances: x collinear with none of R, all orthogonal ones at distance 4
assert not (coll(x) & Rset)
# choose line l_x not in S, with profile (1 concurrent, >= |Nx| at distance 4, >= 756-|Nx| opposite)
while True:
    lx = rng.randrange(N)
    if lx in Sset: continue
    d2, d4 = H.line_ball(lx)
    S2 = Sset & d2; S4 = Sset & d4; S6 = Sset - d2 - d4
    if len(S4) >= len(Nx) and len(S6) >= len(R) - len(Nx): break
print('l_x =', lx, 'S profile', len(S2), len(S4), len(S6))
S4 = sorted(S4); S6 = sorted(S6); rng.shuffle(S4); rng.shuffle(S6)
f = {}
NxS = set(Nx)
it4 = iter(S4); it6 = iter(S6)
for r in R: f[r] = next(it4) if r in NxS else next(it6)
f[x] = lx
Rp = R + [x]
# sigma
sig = -np.ones(N, dtype=np.int64); used = np.zeros(N, dtype=bool)
def assign(p, l):
    assert sig[p] < 0, ('point twice', p); assert not used[l], ('line twice', l)
    sig[p] = l; used[l] = True
for a in Rp: assign(a, f[a])
# midpoints <-> connecting lines for the distance-4 pairs (x, r)
Gx = coll(x); Glx = meet(lx)
for r in Nx:
    mids = Gx & coll(r); cons = Glx & meet(f[r])
    assert len(mids) == 1 and len(cons) == 1, (len(mids), len(cons))
    assign(mids.pop(), cons.pop())
# local duality: rest of Gamma_2(a) -> rest of Gamma_2(f(a))
for a in Rp:
    P = [p for p in coll(a) if sig[p] < 0]; Lns = [l for l in meet(f[a]) if not used[l]]
    assert len(P) == len(Lns), (a, len(P), len(Lns))
    rng.shuffle(Lns)
    for p, l in zip(P, Lns): assign(p, l)
rest_p = [p for p in range(N) if sig[p] < 0]; rest_l = [l for l in range(N) if not used[l]]
assert len(rest_p) == len(rest_l)
rng.shuffle(rest_l)
for p, l in zip(rest_p, rest_l): assign(p, l)
assert (sig >= 0).all() and used.all()
np.savetxt(os.path.join(out, 'sigma.txt'), sig, fmt='%d')
np.savetxt(os.path.join(out, 'R.txt'), np.array(Rp), fmt='%d')
open(os.path.join(out, 'info.txt'), 'w').write(f'seed {seed} x {x} c(x) {len(Nx)} l_x {lx} |R\'| {len(Rp)}\n')
print('wrote', out, '|R\'| =', len(Rp))
