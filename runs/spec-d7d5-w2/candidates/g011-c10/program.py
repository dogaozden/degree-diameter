import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact constructions (unchanged from the parent; they keep calibration cases fast).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New main construction: abelian Haar-type (bi-Cayley, one base pair) graphs.
#
# Vertices: a_x = x (side A), b_y = m + y (side B), for x, y in G = Z_a x Z_b, m = a*b.
# Edges: a_x ~ b_{x+s} for s in S, where S is a set of d distinct group elements.
# This is d-regular and bipartite. By translation and the side-swap automorphism
# a_x <-> b_{-x}, the diameter is at most D iff every element of G is reached
# from a_0 within D steps on both sides.
#
# Search: for each order m (scanned upward from the current best), pick a random
# abelian group of that order and run simulated annealing over S. The cost is the
# number of vertices not reached from a_0 within D steps. Evaluation is a few numpy
# gathers, so thousands of candidate sets are tested per second.
# ----------------------------------------------------------------------------

_M_CAP = 2000  # keeps the m x m translation tables small


def _group_tables(a, b):
    """ADD[t, x] = x + t and SUB[t, x] = x - t for G = Z_a x Z_b, with x = i*b + j."""
    m = a * b
    idx = np.arange(m, dtype=np.int64)
    I = idx // b
    J = idx % b
    ADD = (((I[None, :] + I[:, None]) % a) * b + (J[None, :] + J[:, None]) % b).astype(np.int32)
    SUB = (((I[None, :] - I[:, None]) % a) * b + (J[None, :] - J[:, None]) % b).astype(np.int32)
    return ADD, SUB


def _cost(m, D, ADD, SUB, S):
    """Number of vertices (on both sides) not reached from a_0 within D steps."""
    A = np.zeros(m, dtype=bool)
    B = np.zeros(m, dtype=bool)
    A[0] = True
    AS = SUB[S]  # AS[s, y] = y - s : B-vertex y is reached from A-vertex y - s
    BS = ADD[S]  # BS[s, x] = x + s : A-vertex x is reached from B-vertex x + s
    for _ in range(D):
        nB = A[AS].any(axis=0)
        nA = B[BS].any(axis=0)
        A = A | nA
        B = B | nB
        if A.all() and B.all():
            break
    return int(m - A.sum()) + int(m - B.sum())


def _anneal(d, D, m, ADD, SUB, rng, deadline, iters):
    """Simulated annealing over the connection set S. Returns S as an int array, or None."""
    S = np.array(rng.sample(range(m), d), dtype=np.int64)
    inset = set(int(s) for s in S)
    cost = _cost(m, D, ADD, SUB, S)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (1.0 - t / iters) + 0.05
        p = rng.randrange(d)
        new = rng.randrange(m)
        if new in inset:
            continue
        old = int(S[p])
        S[p] = new
        c2 = _cost(m, D, ADD, SUB, S)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            inset.discard(old)
            inset.add(new)
        else:
            S[p] = old
    if cost == 0:
        return S
    return None


def _edges(m, ADD, S):
    """Edge list of the bi-Cayley graph with 2m vertices."""
    out = []
    for s in S:
        row = ADD[int(s)]
        out.extend((x, m + int(row[x])) for x in range(m))
    return 2 * m, out


def _scan(d, D, best_n, deadline, rng, consider):
    """Scan group orders m upward from the current best, annealing S for each m."""
    m_hi = min(lib.moore_bound(d, D) // 2, _M_CAP)
    m = max(best_n // 2 + 1, d)
    total = max(0.0, deadline - time.monotonic())
    per_m = max(1.0, total / 10.0)
    cache = {}
    while m <= m_hi and time.monotonic() < deadline:
        m_end = min(deadline, time.monotonic() + per_m)
        found = False
        while not found and time.monotonic() < m_end:
            divs = [a for a in range(1, math.isqrt(m) + 1) if m % a == 0]
            a = 1 if rng.random() < 0.5 else rng.choice(divs)
            b = m // a
            key = (a, b)
            if key not in cache:
                if len(cache) >= 4:
                    cache.clear()
                cache[key] = _group_tables(a, b)
            ADD, SUB = cache[key]
            S = _anneal(d, D, m, ADD, SUB, rng, m_end, 4000)
            if S is not None:
                n, e = _edges(m, ADD, S)
                consider(n, e)
                found = True
        m += 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions for calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: abelian bi-Cayley (Haar-type) graphs over scanned group orders.
    if time.monotonic() < deadline:
        _scan(d, D, best_n, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
