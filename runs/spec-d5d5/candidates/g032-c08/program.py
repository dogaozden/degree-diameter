"""Bi-Cayley search for large bipartite graphs with bounded degree and diameter.

New in this version:
  * A numpy oracle for bi-Cayley graphs. Adjacency is a (2N, d) index array, and
    BFS from A_0 and B_0 runs as vectorised frontier expansions.
  * Iterated local search over connection sets. Each sweep tries every
    replacement for one connection element and keeps the best. Random kicks
    escape local optima, which replaces the old random-proposal annealing.
  * Groups are metacyclic Z_m x|_r Z_k (vectorised tables), plus direct
    products of two smaller groups (a family the parent does not use).
  * The order ramps upward from a safe start, so the search keeps trying the
    next order above the best success.
"""
import itertools
import math
import random
import time

import numpy as np

import lib

KICKS = 25          # kicks without improvement before abandoning a group try


# ----------------------------------------------------------------------------
# Baseline families for D = 3 and D = 4 (unchanged from the parent).
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group tables as numpy arrays: T[x, g] = x*g, I[x] = x^{-1}.
# ----------------------------------------------------------------------------

def _divisors(N):
    return [k for k in range(1, N + 1) if N % k == 0]


def _meta_tables(m, k, r):
    """Tables for Z_m x|_r Z_k, element (a, b) coded as a*k + b; (a1,b1)(a2,b2) = (a1 + r^{b1} a2, b1 + b2)."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    T = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    nb = (-b) % k
    inv = ((-pw[nb] * a) % m) * k + nb
    return N, T, inv


def _metacyclic(N, cache):
    """All metacyclic groups Z_m x|_r Z_k of order N as (T, I) tables (cached)."""
    if N in cache:
        return cache[N]
    out = []
    for k in _divisors(N):
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                _, T, I = _meta_tables(m, k, r)
                out.append((T, I))
    cache[N] = out
    return out


def _product(g1, g2):
    """Direct product of two group tables; index of (x1, x2) is x1*N2 + x2."""
    T1, I1 = g1
    T2, I2 = g2
    N1, N2 = T1.shape[0], T2.shape[0]
    N = N1 * N2
    T = (T1[:, None, :, None] * N2 + T2[None, :, None, :]).reshape(N, N)
    I = (I1[:, None] * N2 + I2[None, :]).reshape(N)
    return T, I


def _group_list(N, rng, cache):
    """Metacyclic groups of order N plus a few random direct products with smaller factors."""
    groups = list(_metacyclic(N, cache))
    for N1 in _divisors(N):
        N2 = N // N1
        if N1 < 2 or N2 < 2 or N1 > N2:
            continue
        A = _metacyclic(N1, cache)
        B = _metacyclic(N2, cache)
        if not A or not B:
            continue
        for _ in range(3):
            groups.append(_product(rng.choice(A), rng.choice(B)))
    return groups


# ----------------------------------------------------------------------------
# Vectorised bi-Cayley oracle.
# Vertices A_x = x and B_y = N + y. A_x ~ B_{x s} for s in S (|S| = d).
# Left multiplication is an automorphism, so eccentricities of A_0 and B_0
# decide the diameter.
# ----------------------------------------------------------------------------

def _adjacency(N, T, I, S):
    Sa = np.array(S, dtype=np.int64)
    invS = I[Sa]
    adjA = N + T[:, Sa]      # A_x -> B_{x s}
    adjB = T[:, invS]        # B_y -> A_{y s^{-1}}
    return np.vstack([adjA, adjB])


def _unreached(adj, N, D):
    """Number of (source, vertex) pairs at distance > D, for sources A_0 and B_0."""
    M = 2 * N
    total = 0
    for src in (0, N):
        seen = np.zeros(M, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        count = 1
        for _ in range(D):
            nb = adj[frontier].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            count += nb.size
            frontier = nb
        total += M - count
    return total


def _local(N, T, I, d, D, rng, deadline):
    """Iterated local search over S = {0, s_1, ..., s_{d-1}} minimising unreached pairs."""
    def cost(S):
        return _unreached(_adjacency(N, T, I, S), N, D)

    S = [0] + rng.sample(range(1, N), d - 1)
    cur = cost(S)
    stale = 0
    while True:
        if cur == 0:
            return S
        if time.monotonic() > deadline or stale > KICKS:
            return None
        improved = False
        pos = list(range(1, d))
        rng.shuffle(pos)
        for i in pos:
            best_v, best_c = cur, None
            for c in range(1, N):
                if c in S:
                    continue
                S2 = S[:]
                S2[i] = c
                v = cost(S2)
                if v < best_v:
                    best_v, best_c = v, c
                    if v == 0:
                        break
            if best_c is not None:
                S[i] = best_c
                cur = best_v
                improved = True
            if cur == 0:
                return S
            if time.monotonic() > deadline:
                return None
        if improved:
            stale = 0
        else:
            stale += 1
            for _ in range(rng.randint(1, 2)):
                i = rng.randrange(1, d)
                c = rng.randrange(1, N)
                if c not in S:
                    S[i] = c
            cur = cost(S)


def _attempt(N, d, D, rng, deadline, cache):
    """Round-robin over the groups of order N with growing time slices."""
    groups = _group_list(N, rng, cache)
    if not groups:
        return None
    rng.shuffle(groups)
    slice_t = 0.25
    while time.monotonic() < deadline:
        for T, I in groups:
            now = time.monotonic()
            if now >= deadline:
                break
            dl = min(deadline, now + slice_t)
            S = _local(N, T, I, d, D, rng, dl)
            if S is not None:
                return T, I, S
        slice_t *= 2
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    Nmax = lib._moore_bound(d, D) // 2      # bi-Cayley graph has 2N vertices
    cache = {}
    N = max(d + 1, int(0.45 * Nmax))
    budget = 1.0
    best_N = 0

    while time.monotonic() < deadline and d + 1 <= N <= Nmax:
        now = time.monotonic()
        att_deadline = min(deadline, now + budget)
        res = _attempt(N, d, D, rng, att_deadline, cache)
        if res is not None:
            T, I, S = res
            Sa = np.array(S, dtype=np.int64)
            vals = T[:, Sa]
            edges = [(x, N + int(vals[x, j])) for x in range(N) for j in range(d)]
            consider(2 * N, edges)
            best_N = N
            N += 1
            budget = 1.0
        else:
            if best_N == 0:
                N = max(d + 1, N - 5)
                budget *= 1.5
            else:
                budget *= 2.0      # stuck just above the best order: spend more time

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
