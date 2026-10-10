import itertools
import math
import random
import time

import numpy as np

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _lift_matrix(k, m, darts):
    """Dense symmetric adjacency matrix (float32) of the Z_m voltage lift of the base graph."""
    n = 2 * k * m
    A = np.zeros((n, n), dtype=np.float32)
    g = np.arange(m)
    for u, v, a in darts:
        x = u * m + g
        y = v * m + (g + a) % m
        A[x, y] = 1.0
        A[y, x] = 1.0
    return A


def _bad_pairs_np(A, D):
    """Number of unordered vertex pairs at distance > D, computed by repeated boolean products."""
    n = A.shape[0]
    R = np.eye(n, dtype=np.float32)
    for _ in range(D):
        R = ((R @ A + R) > 0).astype(np.float32)
    reached = int(R.sum())
    return (n * n - reached) // 2


def _anneal(d, D, k, m, rng, iters, deadline):
    """Simulated annealing over Z_m voltages of a random d-regular bipartite base with k+k vertices.

    Returns (n, edges) with zero bad pairs, or None if the budget runs out.
    """
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]
    A = _lift_matrix(k, m, darts)
    c = _bad_pairs_np(A, D)
    T0 = 2.0
    for it in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - it / iters) + 0.2
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = (old + rng.randrange(1, m)) % m
        A2 = _lift_matrix(k, m, darts)
        c2 = _bad_pairs_np(A2, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            A, c = A2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return lib.voltage_lift(2 * k, [tuple(x) for x in darts], m)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # D = 3: projective plane with largest prime power q <= d - 1.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # D >= 4: generalized quadrangle W(q) with q + 1 <= d.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: annealed voltage lifts over larger bases, plus occasional Haar graphs.
    NODE_CAP = 1000  # keep dense matrices small enough to be fast
    base_sizes = [2, 3, 4, 5, 6, 7, 8]
    ladder = {k: 0 for k in base_sizes}
    haar_m, haar_miss = d + 1, 0
    while time.monotonic() < deadline:
        if rng.random() < 0.2 and haar_miss < 4:
            S = _search_haar(d, D, haar_m, rng, deadline, 100)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
            continue

        k = rng.choice(base_sizes)
        m = max(ladder[k], best_n // (2 * k) + 1, 2)
        if 2 * k * m > NODE_CAP:
            # Try a smaller base instead of exceeding the size cap.
            k = 2
            m = max(best_n // (2 * k) + 1, 2)
            if 2 * k * m > NODE_CAP:
                break
        res = _anneal(d, D, k, m, rng, 300, deadline)
        if res is not None:
            consider(res[0], res[1])
            ladder[k] = m + 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
