#!/usr/bin/env python3
"""Extended scorer (card c4): mirror_build.py plus partial stars.
Change w.r.t. mirror_build.py: X may contain distance-4 pairs (orthogonal, non-collinear; the 12 points of a totally
singular non-hexagon line form such a star, all with one common midpoint m).  For every distance-4 pair (a, b) of R + X
the midpoint mu(a, b) (unique point collinear with both) is mapped to the connecting line of (f(a), f(b)); a midpoint
shared by several pairs (the star centre m) must get the same connecting line (checked).  Spread lines meeting such a
connecting line are excluded from the type pool (they would give a second preimage).  Lines of X pairwise at distance 4
iff their points are orthogonal (checked).  Everything else (non-collinearity, mirror of all distance-4 pairs, non-concurrent
image lines, local duality at every a in R + X, bijection) is re-checked as in mirror_build.py.
usage: mirror_build_star.py STATE.npz SEED OUTDIR"""
import numpy as np, sys, os, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
st = np.load(sys.argv[1]); seed = int(sys.argv[2]); out = sys.argv[3]; os.makedirs(out, exist_ok=True)
rng = random.Random(seed)
H = Hex(SP + 'hex_q11.bin'); N = H.N
R = [int(v) for v in st['R']]; Xs = [int(v) for v in st['X']]; Ls = [int(v) for v in st['L']]
S = [int(v) for v in np.load(SP + 'S_herm.npy')]; Sset = set(S)
coll = H.collinear_points; meet = H.lines_meeting
_cc = {}
def collc(a):
    if a not in _cc: _cc[a] = coll(a)
    return _cc[a]
def pdist(a, b):
    if a == b: return 0
    if b in collc(a): return 2
    return 4 if H.B(a, b) == 0 else 6
_lb = {}
def lball(l):
    if l not in _lb: _lb[l] = H.line_ball(l)
    return _lb[l]
def ldist(l1, l2):
    if l1 == l2: return 0
    d2, d4 = lball(l1)
    return 2 if l2 in d2 else (4 if l2 in d4 else 6)
def connecting(l1, l2):
    c = meet(l1) & meet(l2)
    assert len(c) == 1, ('connecting line not unique', len(c))
    return next(iter(c))
k = len(Xs)
# ---- re-check the configuration
assert len(set(R)) == len(R) and len(set(Xs)) == k and len(set(Ls)) == k
Rp = R + Xs
Bm = H.Bmat(np.array(Rp), np.array(Rp)); np.fill_diagonal(Bm, 1)
assert (Bm[:len(R), :len(R)] != 0).all(), 'R not pairwise opposite'
allcoll = set()
for a in Rp: allcoll |= collc(a)
assert not (allcoll & set(Rp)), 'collinear pair in R + X'
for i in range(k):
    assert Ls[i] not in Sset, 'line in S'
    for j in range(i + 1, k):
        want = 4 if pdist(Xs[i], Xs[j]) == 4 else 6
        assert ldist(Ls[i], Ls[j]) == want, ('line/point distance mismatch', i, j)
nstar = sum(1 for i in range(k) for j in range(i + 1, k) if pdist(Xs[i], Xs[j]) == 4)
# ---- types
tR = {r: frozenset(j for j in range(k) if pdist(r, Xs[j]) == 4) for r in R}
balls = [lball(l) for l in Ls]
excluded = set()
for j, (d2, d4) in enumerate(balls):
    excluded |= {s for s in d2 if s in Sset}
conn_lines = set()
for i in range(k):
    for j in range(i + 1, k):
        if pdist(Xs[i], Xs[j]) == 4: conn_lines.add(connecting(Ls[i], Ls[j]))
for Nn in conn_lines:
    excluded |= {s for s in meet(Nn) if s in Sset}
    excluded |= {s for s in [Nn] if s in Sset}
tS = {}
for s in S:
    if s in excluded: continue
    tS[s] = frozenset(j for j, (d2, d4) in enumerate(balls) if s in d4)
poolS = collections.defaultdict(list)
for s in S:
    if s not in excluded: poolS[tS[s]].append(s)
cntR = collections.Counter(tR.values())
dropped = []; keepR = []
left = {t: len(poolS[t]) for t in cntR}
for r in R:
    if left[tR[r]] > 0: left[tR[r]] -= 1; keepR.append(r)
    else: dropped.append(r)
R = keepR
f = {}
for t in poolS: rng.shuffle(poolS[t])
for r in R: f[r] = poolS[tR[r]].pop()
for j in range(k): f[Xs[j]] = Ls[j]
Rp = R + Xs
Bm = H.Bmat(np.array(Rp), np.array(Rp)); np.fill_diagonal(Bm, 1)
# ---- mirror check: for every a, the image lines within distance 4 of f(a) are exactly f of the points orthogonal to a
fl = {f[a]: a for a in Rp}
assert len(fl) == len(Rp), 'image lines not distinct'
for ia, a in enumerate(Rp):
    d2, d4 = H.line_ball(f[a])
    assert not (d2 & set(fl)), ('concurrent image lines', a)
    near = {fl[l] for l in d4 if l in fl}
    orth = {Rp[j] for j in np.nonzero(Bm[ia] == 0)[0]}
    assert near == orth, ('mirror fails at', a, len(near), len(orth))
# ---- sigma
sig = -np.ones(N, dtype=np.int64); used = np.zeros(N, dtype=bool)
def assign(p, l):
    assert sig[p] < 0 and not used[l], (p, l)
    sig[p] = l; used[l] = True
for a in Rp: assign(a, f[a])
mid_line = {}
npairs = 0
for ia in range(len(Rp)):
    for ib in range(ia + 1, len(Rp)):
        a, b = Rp[ia], Rp[ib]
        if pdist(a, b) != 4: continue
        mu = collc(a) & collc(b); assert len(mu) == 1
        mu = next(iter(mu))
        Nn = connecting(f[a], f[b])
        if mu in mid_line:
            assert mid_line[mu] == Nn, ('midpoint with two connecting lines', mu)
            continue
        assign(mu, Nn); mid_line[mu] = Nn; npairs += 1
for a in Rp:
    for p in collc(a):
        if sig[p] >= 0:
            assert sig[p] in meet(f[a]) or sig[p] == f[a], ('local duality violated at', a)
    P = [p for p in collc(a) if sig[p] < 0]; Lns = [l for l in meet(f[a]) if not used[l]]
    assert len(P) == len(Lns), (a, len(P), len(Lns))
    rng.shuffle(Lns)
    for p, l in zip(P, Lns): assign(p, l)
rest_p = np.nonzero(sig < 0)[0].tolist(); rest_l = np.nonzero(~used)[0].tolist()
rng.shuffle(rest_l)
for p, l in zip(rest_p, rest_l): assign(p, l)
assert (sig >= 0).all() and used.all()
np.savetxt(os.path.join(out, 'sigma.txt'), sig, fmt='%d')
np.savetxt(os.path.join(out, 'R.txt'), np.array(Rp), fmt='%d')
with open(os.path.join(out, 'config.txt'), 'w') as g:
    g.write(f'# mirrored surgery set (partial stars allowed): {len(R)} points of the base set (dropped {len(dropped)}) + {k} extra points; {npairs} distinct midpoints, {nstar} X-internal distance-4 pairs\n')
    g.write('D ' + ' '.join(map(str, dropped)) + '\n')
    g.write('X ' + ' '.join(map(str, Xs)) + '\nL ' + ' '.join(map(str, Ls)) + '\n')
print(f'|R\'| = {len(Rp)} (dropped {len(dropped)} of the base set, added {k}), distance-4 pairs {npairs}, X-internal {nstar}, types used {len(cntR)}; wrote {out}')
