#!/usr/bin/env python3
"""Bipartite route-chart lifts (adapting Mizuno, arXiv:2606.15860, to the bipartite problem).

Controller: Haar graph H(G, S), |S| = 4: (g, A) ~ (s g, B).  Fiber F_4^4.  Lift: (g, x)_A ~ (s g, A_s x + lam b_s)_B,
lam in F_4.  16-regular, bipartite, 2|G| 4^4 vertices.

A nonbacktracking walk of length 4 from (g,A) with letter indices i1 != i2 != i3 != i4 ends at
(s_{i4}^-1 s_{i3} s_{i2}^-1 s_{i1} g, A); from (h,B) at (s_{i4} s_{i3}^-1 s_{i2} s_{i1}^-1 h, B).
Diameter <= 5 if every element of G is such a word on both sides and the chart makes every controllability matrix of
a used walk nonsingular (then a lifted walk of length 4 reaches every fiber point; opposite sides follow).

This file: controller search (exact-NB-4 coverage) over small groups given by multiplication tables.
usage: python3 controller.py search <group spec> <seconds> <seed>
group specs: meta a b r  (Z_a x| Z_b, b acts by t -> r t; m = ab) | dih n | cyc n | prod <spec> x <spec>
"""
import sys, time, random, itertools
import numpy as np

WORDS = [w for w in itertools.product(range(4), repeat=4)
         if w[0] != w[1] and w[1] != w[2] and w[2] != w[3]]
assert len(WORDS) == 108


def meta(a, b, r):
    assert pow(r, b, a) == 1 % a
    els = [(x, y) for y in range(b) for x in range(a)]
    idx = {e: k for k, e in enumerate(els)}
    m = len(els)
    T = np.empty((m, m), dtype=np.int32)
    for i, (x, y) in enumerate(els):
        ry = pow(r, y, a)
        for j, (u, v) in enumerate(els):
            T[i, j] = idx[((x + ry * u) % a, (y + v) % b)]
    return T


def table_from_perms(gens):
    """closure of permutation generators (tuples); returns multiplication table (p*q means apply q first? we use
    composition (p*q)[k] = p[q[k]])."""
    n = len(gens[0])
    e = tuple(range(n))
    els = [e]; idx = {e: 0}
    k = 0
    while k < len(els):
        g = els[k]
        for s in gens:
            h = tuple(g[s[i]] for i in range(n))
            if h not in idx:
                idx[h] = len(els); els.append(h)
        k += 1
    m = len(els)
    T = np.empty((m, m), dtype=np.int32)
    for i, g in enumerate(els):
        for j, h in enumerate(els):
            T[i, j] = idx[tuple(g[h[t]] for t in range(n))]
    return T


def product(T1, T2):
    m1, m2 = len(T1), len(T2)
    m = m1 * m2
    T = np.empty((m, m), dtype=np.int32)
    for i in range(m):
        a1, a2 = divmod(i, m2)
        T[i] = T1[a1][np.arange(m) // m2] * m2 + T2[a2][np.arange(m) % m2]
    return T


def parse(spec):
    toks = spec.split()
    if 'x' in toks:
        k = toks.index('x')
        return product(parse(' '.join(toks[:k])), parse(' '.join(toks[k + 1:])))
    if toks[0] == 'meta':
        return meta(*map(int, toks[1:4]))
    if toks[0] == 'cyc':
        n = int(toks[1]); return meta(n, 1, 1)
    if toks[0] == 'dih':
        n = int(toks[1]); return meta(n, 2, n - 1)
    raise ValueError(spec)


class Group:
    def __init__(self, T):
        self.T = T; self.m = len(T)
        e = [i for i in range(self.m) if (T[i] == np.arange(self.m)).all()]
        self.e = e[0]
        self.inv = np.empty(self.m, dtype=np.int32)
        for i in range(self.m):
            self.inv[i] = int(np.nonzero(T[i] == self.e)[0][0])


def coverage(Gr, S):
    T, inv = Gr.T, Gr.inv
    Si = [int(inv[s]) for s in S]
    covA = np.zeros(Gr.m, dtype=bool); covB = np.zeros(Gr.m, dtype=bool)
    for (i1, i2, i3, i4) in WORDS:
        # A side: s_i4^-1 s_i3 s_i2^-1 s_i1 ; B side: s_i4 s_i3^-1 s_i2 s_i1^-1
        a = T[Si[i4], T[S[i3], T[Si[i2], S[i1]]]]
        b = T[S[i4], T[Si[i3], T[S[i2], Si[i1]]]]
        covA[a] = True; covB[b] = True
    return covA, covB


def cost(Gr, S):
    a, b = coverage(Gr, S)
    return (Gr.m - a.sum()) + (Gr.m - b.sum())


def search(Gr, seconds, seed):
    rng = random.Random(seed)
    m = Gr.m
    S = [Gr.e] + rng.sample([x for x in range(m) if x != Gr.e], 3)
    c = cost(Gr, S); best = (c, list(S))
    t0 = time.time(); it = 0
    while time.time() - t0 < seconds and best[0] > 0:
        it += 1
        S2 = list(S)
        k = rng.randrange(1, 4)
        S2[k] = rng.randrange(m)
        if len(set(S2)) < 4:
            continue
        c2 = cost(Gr, S2)
        if c2 <= c or rng.random() < 0.02:
            S, c = S2, c2
            if c < best[0]:
                best = (c, list(S))
    return best, it


if __name__ == '__main__':
    if sys.argv[1] == 'search':
        T = parse(sys.argv[2]); Gr = Group(T)
        best, it = search(Gr, float(sys.argv[3]), int(sys.argv[4]))
        print(f'group "{sys.argv[2]}" m={Gr.m} cost={best[0]} S={best[1]} iters={it}', flush=True)
