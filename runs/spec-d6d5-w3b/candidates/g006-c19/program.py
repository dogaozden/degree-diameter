"""Bold rewrite: bi-Cayley Haar-type graphs over non-abelian groups.

Construction: pick a finite group G of order n/2 (cyclic or Z_m x|_r Z_k), a set S of
d distinct group elements containing the identity, and join a_x to b_{x*s} for s in S.
Left multiplication is an automorphism that is transitive on each side, so the diameter
is verified by two BFS runs (from a_e and from b_e) over numpy boolean arrays. Search is
simulated annealing over S, with the group order chosen in a window just above the
current best. A K_{d,d} fallback is kept and every returned graph is checked with lib.is_valid.
"""
import math
import random
import time

import numpy as np

import lib


def _row_table(G, mul):
    """Cached right-multiplication tables: rt(s)[x] = x * s."""
    cache = {}

    def rt(s):
        t = cache.get(s)
        if t is None:
            t = np.array([mul(x, s) for x in range(G)], dtype=np.int64)
            cache[s] = t
        return t

    return rt


def _cost(G, D, rows, irows):
    """Number of (source, vertex) pairs at distance > D from a_e and b_e. Zero means valid."""
    total = 0
    for start_on_a in (True, False):
        visA = np.zeros(G, dtype=bool)
        visB = np.zeros(G, dtype=bool)
        front = np.zeros(1, dtype=np.int64)
        if start_on_a:
            visA[0] = True
        else:
            visB[0] = True
        on_a = start_on_a
        for _ in range(D):
            if front.size == 0:
                break
            mask = np.zeros(G, dtype=bool)
            if on_a:
                # a_x ~ b_{x s}
                for r in rows:
                    mask[r[front]] = True
                new = mask & ~visB
                visB |= new
            else:
                # b_y ~ a_{y s^-1}
                for r in irows:
                    mask[r[front]] = True
                new = mask & ~visA
                visA |= new
            front = np.flatnonzero(new)
            on_a = not on_a
        total += 2 * G - int(visA.sum()) - int(visB.sum())
    return total


def _eval(G, D, S, rt, inv):
    rows = [rt(s) for s in S]
    irows = [rt(inv(s)) for s in S]
    return _cost(G, D, rows, irows)


def _anneal(d, D, G, rt, inv, rng, deadline, iters):
    """Anneal a set S = {identity} + (d-1) other group elements. Returns S or None."""
    others = list(range(1, G))
    S = [0] + rng.sample(others, d - 1)
    c = _eval(G, D, S, rt, inv)
    T = 1.0
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        new = rng.randrange(1, G)
        if new in S:
            continue
        S2 = S[:]
        S2[i] = new
        c2 = _eval(G, D, S2, rt, inv)
        T = max(0.05, T * 0.995)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = S2, c2
    return S if c == 0 else None


def _sample_group(G, rng):
    """Random group of order G as Z_m x|_r Z_k (k=1 gives cyclic Z_G)."""
    divs = [k for k in range(1, min(G, 24) + 1) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    if rng.random() < 0.3:
        k = 1
    else:
        k = rng.choice(divs)
    m = G // k
    if k == 1:
        r = 1
    else:
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
    try:
        order, mul, inv = lib.semidirect_group(m, k, r)
    except ValueError:
        return None
    return order, mul, inv


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, 0.85 * time_limit - 1.0)
    deadline = start + budget
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2 <= D.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)

    moore = lib.moore_bound(d, D)
    half_moore = moore // 2

    while time.monotonic() < deadline:
        lo = max(d, best_n // 2 + 1)
        if lo > half_moore:
            break
        hi = max(lo, min(half_moore, best_n // 2 + 40))
        G = rng.randint(lo, hi)

        grp = _sample_group(G, rng)
        if grp is None:
            continue
        order, mul, inv = grp
        if order < d:
            continue
        rt = _row_table(order, mul)

        S = _anneal(d, D, order, rt, inv, rng, deadline, iters=500)
        if S is None:
            continue

        n = 2 * order
        if n <= best_n:
            continue
        rows = [rt(s) for s in S]
        edges = [(x, order + int(row[x])) for row in rows for x in range(order)]
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_n = n

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
