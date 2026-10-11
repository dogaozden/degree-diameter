"""Bi-Cayley (Haar-type) search for bipartite graphs of max degree d and diameter D.

Construction: take a finite group H of order G and k base orbits on each side.
Vertices are A_{i,h} = i*G + h and B_{j,h} = (k+j)*G + h. For each (i, j) pick a set
S_ij of group elements, and join A_{i,h} to B_{j,h*s} for every s in S_ij.
Left translation by H is an automorphism, so distances only need to be checked
from the k + k base vertices A_{i,1} and B_{j,1}. Row and column sums of |S_ij|
equal d, so the graph is d-regular and bipartite by construction.

Each candidate is annealed over connection-set entries (for k = 1 the identity is
fixed WLOG). Every output is checked with lib.is_valid. Fallbacks are K_{d,d}
(valid for D >= 2) and the projective-plane incidence graph (valid for D >= 3).
Not executed in this session; correctness relies on the lib.is_valid gate.
"""
import math
import random
import time

import lib


_TABLES = {}


def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (m, k2, r), or None."""
    divs = [k2 for k2 in range(1, 13) if G % k2 == 0]
    rng.shuffle(divs)
    for k2 in divs:
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            rs = [1]
        else:
            rs = [r for r in range(1, m)
                  if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if rs:
            return m, k2, rng.choice(rs)
    return None


def _table(m, k2, r):
    """Multiplication table T[x][y] and inverse list for the group (cached, small cache)."""
    key = (m, k2, r)
    hit = _TABLES.get(key)
    if hit is not None:
        return hit
    G, mul, inv = lib.semidirect_group(m, k2, r)
    T = [[mul(x, y) for y in range(G)] for x in range(G)]
    IV = [inv(x) for x in range(G)]
    if len(_TABLES) >= 6:
        _TABLES.clear()
    _TABLES[key] = (G, T, IV)
    return G, T, IV


def _cost(k, G, T, IV, S, D):
    """Total number of (source, vertex) pairs not reached within distance D. Zero means valid."""
    N = 2 * k * G
    kG = k * G
    srcs = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in srcs:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < kG:
                    i, h = divmod(u, G)
                    row = T[h]
                    for j in range(k):
                        base = (k + j) * G
                        for s in S[i][j]:
                            v = base + row[s]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                else:
                    j, x = divmod(u - kG, G)
                    row = T[x]
                    for i in range(k):
                        base = i * G
                        for s in S[i][j]:
                            v = base + row[IV[s]]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, T, S):
    """Full edge list of the bi-Cayley graph described by S."""
    E = []
    for i in range(k):
        for j in range(k):
            for s in S[i][j]:
                for h in range(G):
                    E.append((i * G + h, (k + j) * G + T[h][s]))
    return 2 * k * G, E


def _anneal(k, G, T, IV, sz, d, D, rng, deadline, iters):
    """Simulated annealing over connection sets. Returns (cost, S)."""
    if k == 1:
        S = [[[0] + rng.sample(range(1, G), d - 1)]]
    else:
        S = [[rng.sample(range(G), sz[i][j]) if sz[i][j] else []
              for j in range(k)] for i in range(k)]
    cells = [(i, j) for i in range(k) for j in range(k) if sz[i][j] > 0]
    cost = _cost(k, G, T, IV, S, D)
    temp = 1.0
    lo_p = 1 if k == 1 else 0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i, j = rng.choice(cells)
        lst = S[i][j]
        if len(lst) <= lo_p:
            continue
        p = rng.randrange(lo_p, len(lst))
        c = rng.randrange(G)
        if c in lst:
            continue
        old = lst[p]
        lst[p] = c
        c2 = _cost(k, G, T, IV, S, D)
        temp = max(0.05, temp * 0.996)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            lst[p] = old
    return cost, S


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}. It is optimal for D = 2 (Moore bound 2d).
    hn, he = lib.haar_graph(d, range(d))
    holder = [hn, he]
    if D == 2 or d == 1:
        return holder[0], holder[1]

    def consider(n, e):
        if n > holder[0] and lib.is_valid(n, e, d, D):
            holder[0], holder[1] = n, e

    pg = _pg(d)
    if pg is not None:
        if pg[0] == lib.moore_bound(d, D) and lib.is_valid(pg[0], pg[1], d, D):
            return pg[0], pg[1]   # calibration: meets the Moore bound, return instantly
        consider(pg[0], pg[1])

    rng = random.Random(seed * 1000003 + d * 101 + D)
    deadline = t0 + max(0.3, min(0.8 * time_limit, time_limit - 3.0))

    while time.monotonic() < deadline:
        k = 1 if rng.random() < 0.7 else 2
        best_n = holder[0]
        lo = max(2, best_n // (2 * k) + 1)
        G = lo + rng.randrange(0, 1 + max(2, lo // 40))
        if G < d:
            continue
        g = _sample_group(G, rng)
        if g is None:
            continue
        Gt, T, IV = _table(*g)
        if k == 1:
            sz = [[d]]
        else:
            a = rng.randint(0, d)
            sz = [[a, d - a], [d - a, a]]
        if max(max(row) for row in sz) > Gt:
            continue
        gd = min(deadline, time.monotonic() + 6.0)
        cost, S = _anneal(k, Gt, T, IV, sz, d, D, rng, gd, 700 if k == 1 else 900)
        if cost == 0:
            n, e = _edges(k, Gt, T, S)
            consider(n, e)

    if not lib.is_valid(holder[0], holder[1], d, D):
        hn, he = lib.haar_graph(d, range(d))
        return hn, he
    return holder[0], holder[1]
