#!/usr/bin/env python3
"""Build sigma (DUALFILE for research/d13D7/multi.c) from a mirrored configuration:
R (pairwise opposite points), X (extra points, pairwise opposite, non-collinear with R), L (one line per X point,
pairwise opposite, not in the Hermitian spread S).  f: R -> S is any type-preserving injection (type of r = the set
of j with d(r, X_j) = 4; type of a spread line s = the set of j with d(s, L_j) = 4; spread lines concurrent with
some L_j are not used).  sigma maps R + X to f(R) + L, every midpoint of a distance-4 pair (r, X_j) to the connecting
line of (f(r), L_j), the rest of Gamma_2(a) onto the rest of Gamma_2(sigma(a)) for every a in R + X, and the remaining
points to the remaining lines; all choices seeded.  Every hypothesis is re-checked here and again by multi.c.
usage: mirror_build_g.py STATE.npz SEED OUTDIR [SPREAD.npy]  (SPREAD defaults to S_herm)"""
import numpy as np, sys, os, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
st = np.load(sys.argv[1]); seed = int(sys.argv[2]); out = sys.argv[3]; os.makedirs(out, exist_ok=True)
rng = random.Random(seed)
H = Hex(SP + 'hex_q11.bin'); N = H.N
R = [int(v) for v in st['R']]; Xs = [int(v) for v in st['X']]; Ls = [int(v) for v in st['L']]
S = [int(v) for v in np.load(sys.argv[4] if len(sys.argv) > 4 else SP + 'S_herm.npy')]
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
def ldist(l1, l2):
    if l1 == l2: return 0
    if l1 not in _lb: _lb[l1] = H.line_ball(l1)
    d2, d4 = _lb[l1]
    return 2 if l2 in d2 else (4 if l2 in d4 else 6)
# re-check the configuration
Rp = R + Xs
Bm = H.Bmat(np.array(Rp), np.array(Rp)); np.fill_diagonal(Bm, 1)
assert (Bm[:len(R), :len(R)] != 0).all(), 'R not pairwise opposite'
assert (Bm[len(R):, len(R):] != 0).all(), 'X not pairwise opposite'
allcoll = set()
for a in Rp: allcoll |= collc(a)
assert not (allcoll & set(Rp)), 'collinear pair in R + X'
for i in range(len(Ls)):
    assert Ls[i] not in set(S)
    for j in range(i + 1, len(Ls)): assert ldist(Ls[i], Ls[j]) == 6
# types
k = len(Xs)
tR = {r: frozenset(j for j in range(k) if pdist(r, Xs[j]) == 4) for r in R}
balls = [H.line_ball(l) for l in Ls]
tS = {}; excluded = set()
for s in S:
    t = set()
    for j, (d2, d4) in enumerate(balls):
        if s in d2: excluded.add(s)
        elif s in d4: t.add(j)
    tS[s] = frozenset(t)
poolS = collections.defaultdict(list)
for s in S:
    if s not in excluded: poolS[tS[s]].append(s)
cntR = collections.Counter(tR.values())
# R points of a type with too few spread lines are dropped (R' = R minus D plus X); the rest keep their order
dropped = []
keepR = []
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
# mirrored distances check
# mirrored distances: for every a, the lines of f(R') within distance 4 of f(a) are exactly f of the points of R'
# orthogonal to a (no collinear pairs, so orthogonal = distance 4)
fl = {f[a]: a for a in Rp}
for ia, a in enumerate(Rp):
    d2, d4 = H.line_ball(f[a])
    assert not (d2 & set(fl)), ('concurrent lines', a)
    near = {fl[l] for l in d4 if l in fl}
    orth = {Rp[j] for j in np.nonzero(Bm[ia] == 0)[0]}
    assert near == orth, ('mirror fails at', a, len(near), len(orth))
sig = -np.ones(N, dtype=np.int64); used = np.zeros(N, dtype=bool)
def assign(p, l):
    assert sig[p] < 0 and not used[l], (p, l)
    sig[p] = l; used[l] = True
for a in Rp: assign(a, f[a])
npairs = 0
for j, x in enumerate(Xs):
    Gx = coll(x); Gl = meet(Ls[j])
    for r in R:
        if j in tR[r]:
            m = Gx & coll(r); M = Gl & meet(f[r])
            assert len(m) == 1 and len(M) == 1
            assign(m.pop(), M.pop()); npairs += 1
for a in Rp:
    P = [p for p in coll(a) if sig[p] < 0]; Lns = [l for l in meet(f[a]) if not used[l]]
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
    g.write(f'# mirrored surgery set: {len(R)} points of the base set (dropped {len(dropped)}) + {k} extra points; {npairs} distance-4 pairs\n')
    g.write('D ' + ' '.join(map(str, dropped)) + '\n')
    g.write('X ' + ' '.join(map(str, Xs)) + '\nL ' + ' '.join(map(str, Ls)) + '\n')
print(f'|R\'| = {len(Rp)} (dropped {len(dropped)} of the base set, added {k}), distance-4 pairs {npairs}, types used {len(cntR)}; wrote {out}')
