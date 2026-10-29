#!/usr/bin/env python3
"""Cluster-assisted Haar hub graphs for the typed layouts (research/synthetic/conics2/README.md; the idea of
research/squads/cells/d12D7.md Section 2). G = PSL(2,p); line-side hub x ~ point-side hub x s for s in S (|S| = DEG).
Two line-side hubs x, x w are within distance 6 in the hub graph iff w in (S S^-1)^3. In a "cluster level" the hubs of
each left coset x H (H a small cyclic subgroup) take free slots at points of ONE spread line (points pairwise at
distance <= 2 in the hexagon), so these hubs are within distance 4 through the level: right multiplication by H.
Every same-side pair is then within 6 if every element of G lies in
   line side:  (S S^-1)^{<=3} u C_A u C_A (S S^-1) u (S S^-1) C_A u S C_B S^-1
   point side: (S^-1 S)^{<=3} u C_B u C_B (S^-1 S) u (S^-1 S) C_B u S^-1 C_A S
(C_A, C_B = unions of the subgroups of the line-side and point-side cluster levels). This is a sufficient condition;
the builder output is checked independently with research/d15D7b/hubfar.c and the all-pairs check.
Hill climbing on S and on the subgroup generators (orders in ORDS) until both sides are covered.
Output: first line K = |G|; "S ..." (matrices); "A <ord> <generator index>" / "B ..." per cluster level; then the hub
graph edges "a b" (line-side a, point-side b); and OUT.cosets: per cluster level one line "A|B <coset id per hub>".
usage: clhub.py p DEG nA nB ORDS SEED OUT [ITERS]       (ORDS e.g. 12,15,16: allowed subgroup orders)"""
import sys
import itertools
import numpy as np

p, DEG, nA, nB = (int(a) for a in sys.argv[1:5])
ORDS = [int(t) for t in sys.argv[5].split(',')]
seed, out = int(sys.argv[6]), sys.argv[7]
ITERS = int(sys.argv[8]) if len(sys.argv) > 8 else 3000
els = [e for e in itertools.product(range(p), repeat=4) if (e[0] * e[3] - e[1] * e[2]) % p == 1]
E = np.array(els, dtype=np.int64)


def canon(M):
    M = M % p
    first = M[np.arange(len(M)), np.argmax(M != 0, axis=1)]
    flip = first > (p - 1) // 2
    M[flip] = (-M[flip]) % p
    return M


def code(M):
    return ((M[:, 0] * p + M[:, 1]) * p + M[:, 2]) * p + M[:, 3]


C = np.unique(code(canon(E)))
G = len(C)
EL = np.stack([C // p ** 3, (C // p ** 2) % p, (C // p) % p, C % p], axis=1)
ident = int(np.searchsorted(C, code(canon(np.array([[1, 0, 0, 1]])))[0]))


def rmul(X, m):                                         # rows of X (k x 4) times matrix m, as indices
    a, b, c, d = m
    Y = np.stack([X[:, 0] * a + X[:, 1] * c, X[:, 0] * b + X[:, 1] * d, X[:, 2] * a + X[:, 3] * c,
                  X[:, 2] * b + X[:, 3] * d], axis=1)
    return np.searchsorted(C, code(canon(Y)))


def inv(i):
    a, b, c, d = EL[i]
    return int(np.searchsorted(C, code(canon(np.array([[d, -b, -c, a]])))[0]))


def prod(A, B):                                         # {a b : a in A, b in B} (index arrays)
    if len(A) == 0 or len(B) == 0:
        return np.zeros(0, np.int64)
    return np.unique(np.concatenate([rmul(EL[A], tuple(EL[b])) for b in B]))


def cyclic(g):
    H = [ident]; x = g
    while x != ident:
        H.append(x); x = int(rmul(EL[[x]], tuple(EL[g]))[0])
    return np.array(H, dtype=np.int64)


def coverage(S, HA, HB):
    Si = np.array([inv(s) for s in S])
    res = []
    for side in (0, 1):
        D = prod(np.array(S), Si) if side == 0 else prod(Si, np.array(S))
        perms = [rmul(EL, tuple(EL[d])) for d in D]
        reach = np.zeros(G, bool); reach[ident] = True
        for _ in range(3):
            idx = np.nonzero(reach)[0]; new = reach.copy()
            for P in perms:
                new[P[idx]] = True
            reach = new
        own = np.unique(np.concatenate(HA if side == 0 else HB)) if (HA if side == 0 else HB) else np.zeros(0, np.int64)
        oth = np.unique(np.concatenate(HB if side == 0 else HA)) if (HB if side == 0 else HA) else np.zeros(0, np.int64)
        cov = reach.copy()
        if len(own):
            cov[own] = True; cov[prod(own, D)] = True; cov[prod(D, own)] = True
        if len(oth):
            a, b = (np.array(S), Si) if side == 0 else (Si, np.array(S))
            cov[prod(prod(a, oth), b)] = True
        res.append(int(G - cov.sum()))
    return res


rng = np.random.default_rng(seed)
order = {}


def rand_gen():                                         # a random element of an allowed order
    while True:
        g = int(rng.integers(G))
        if g not in order:
            order[g] = len(cyclic(g))
        if order[g] in ORDS:
            return g


S = [int(i) for i in rng.choice(G, size=DEG, replace=False)]
gA = [rand_gen() for _ in range(nA)]; gB = [rand_gen() for _ in range(nB)]
HA = [cyclic(g) for g in gA]; HB = [cyclic(g) for g in gB]
miss = coverage(S, HA, HB); cost = sum(miss)
print(f'PSL(2,{p}), |G| = {G}, degree {DEG}, cluster levels {nA} + {nB}, orders {ORDS}: start missing {miss}', flush=True)
it = 0
while cost > 0 and it < ITERS:
    it += 1
    S2, gA2, gB2 = list(S), list(gA), list(gB)
    r = rng.random()
    if r < 0.5 or nA + nB == 0:
        S2[rng.integers(DEG)] = int(rng.integers(G))
        if len(set(S2)) < DEG:
            continue
    elif r < 0.75 and nA:
        gA2[rng.integers(nA)] = rand_gen()
    elif nB:
        gB2[rng.integers(nB)] = rand_gen()
    else:
        continue
    HA2 = [cyclic(g) for g in gA2]; HB2 = [cyclic(g) for g in gB2]
    m2 = coverage(S2, HA2, HB2)
    if sum(m2) <= cost:
        if sum(m2) < cost:
            print(f'  step {it}: missing {m2}', flush=True)
        S, gA, gB, HA, HB, miss, cost = S2, gA2, gB2, HA2, HB2, m2, sum(m2)
assert cost == 0, f'not covered: missing {miss}'
with open(out, 'w') as f:
    f.write(f'{G}\nS ' + ' '.join(str(tuple(int(v) for v in EL[s])).replace(' ', '') for s in S) + '\n')
    for side, gs in (('A', gA), ('B', gB)):
        for g in gs:
            f.write(f'{side} {len(cyclic(g))} {tuple(int(v) for v in EL[g])}\n'.replace(', ', ','))
    for s in S:
        img = rmul(EL, tuple(EL[s]))
        for x in range(G):
            f.write(f'{x} {int(img[x])}\n')
with open(out + '.cosets', 'w') as f:                  # coset id of every hub (= group element) per cluster level
    for side, Hs in (('A', HA), ('B', HB)):
        for H in Hs:                                # left coset x H; its least element index is its id
            cid = np.min(np.stack([rmul(EL, tuple(EL[h])) for h in H]), axis=0)
            cid = np.unique(cid, return_inverse=True)[1]
            assert np.bincount(cid).min() == len(H) == np.bincount(cid).max()
            f.write(f'{side} {len(H)} ' + ' '.join(map(str, cid)) + '\n')
print(f'covered after {it} steps: S = {[tuple(int(v) for v in EL[s]) for s in S]}, A orders '
      f'{[len(h) for h in HA]}, B orders {[len(h) for h in HB]}; wrote {out} and {out}.cosets', flush=True)
