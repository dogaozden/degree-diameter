#!/usr/bin/env python3
"""Greedy partial ovoid (pairwise opposite points) of H(q) from a hexgen2 .bin, for the non-friendly surgery of
typed_build.py (Corollary 5.3(a) of D7_HEXAGON.md). Opposite = not orthogonal for the polar form of Q(6,q) (D7_HEXAGON.md
(F4)); the script first compares this with incidence-graph distances (ball of radius 4) at 20 random points, and the
builder re-checks the final set with balls of radius 4.
usage: ovoid_greedy.py HEXBIN SEED TRIES OUT"""
import sys
import numpy as np
sys.path.insert(0, __import__('os').path.dirname(__file__))
from typed_build import F

hexfn, seed, tries, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
b = open(hexfn, 'rb').read()
q, N, Lc = (int(t) for t in np.frombuffer(b[:12], dtype=np.int32))
LP = np.frombuffer(b[12:12 + 4 * Lc * (q + 1)], dtype=np.int32).reshape(Lc, q + 1).astype(np.int64)
X = np.frombuffer(b[12 + 4 * Lc * (q + 1):], dtype=np.uint8).reshape(N, 7).astype(np.int64)
flat_p = LP.reshape(-1); flat_l = np.repeat(np.arange(Lc), q + 1)
PL = flat_l[np.lexsort((flat_l, flat_p))].reshape(N, q + 1)
Fq = F(q)
pairs = [(0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2)]


def polar(i):                                          # b(X[i], X[y]) for all y (the X3 term 2 x3 y3, odd q only)
    x = X[i]; acc = np.zeros(N, np.int64)
    for a, c in pairs:
        acc = Fq.add(acc, Fq.mul(x[a], X[:, c]))
    if Fq.p != 2:
        acc = Fq.sub(acc, Fq.mul(Fq.add(x[3], x[3]), X[:, 3]))
    return acc


rng = np.random.default_rng(seed)
for i in rng.choice(N, 20, replace=False):              # (F4) sanity check against the incidence graph
    b2 = np.unique(LP[PL[i]].reshape(-1)); b4 = np.unique(LP[PL[b2].reshape(-1)].reshape(-1))
    assert np.array_equal(np.sort(b4), np.nonzero(polar(i) == 0)[0]), 'F4 fails'
print(f'q = {q}: (F4) agrees with the incidence graph at 20 random points', flush=True)
best = []
for t in range(tries):
    avail = np.ones(N, bool); R = []
    order = rng.permutation(N); k = 0
    while True:
        while k < N and not avail[order[k]]:
            k += 1
        if k == N:
            break
        i = int(order[k]); R.append(i); avail &= polar(i) != 0
    print(f'try {t}: {len(R)} pairwise opposite points', flush=True)
    if len(R) > len(best):
        best = R
open(out, 'w').write(' '.join(str(i) for i in sorted(best)) + '\n')
print(f'best {len(best)} -> {out}')
