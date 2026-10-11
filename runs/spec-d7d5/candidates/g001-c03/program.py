import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact baseline families.
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
# Bi-Cayley lifts over semidirect products, searched with a matrix-power
# reachability cost.
#
# New helper: the reach-set cost is computed by repeated boolean-style matrix
# products on the 2k orbit representatives (R <- min(1, R + R A)), rather than
# per-vertex Python BFS. The lift is vertex-transitive within each side, so
# reaching everything from the 2k representatives within D steps is exactly
# the diameter condition.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h.
# Dart (i, j, s) joins A_{i,g} to B_{j,g*s} for every g in the group.
# ----------------------------------------------------------------------------

_PENALTY = 1000


def _sample_group(target, rng):
    """Random semidirect product Z_m x| Z_k2 with order >= target (or None)."""
    for _ in range(300):
        k2 = rng.choice([1, 1, 2, 2, 3, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(80):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Anneal the voltages of a bi-Cayley base with k vertices per side.

    Each of the d layers is a permutation of range(k), so every vertex has degree d.
    Returns (n, edges) with diameter <= D, or None.
    """
    N = 2 * k * G
    ar = np.arange(G, dtype=np.int64)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    rep_idx = np.arange(len(reps))

    def perm_for(s):
        return np.fromiter((mul(g, s) for g in range(G)), dtype=np.int64, count=G)

    def build_A(darts, perms):
        A = np.zeros((N, N), dtype=np.float32)
        for (i, j, _s), pm in zip(darts, perms):
            a = i * G + ar
            b = (k + j) * G + pm
            A[a, b] = 1.0
            A[b, a] = 1.0
        return A

    def reach_cost(A):
        # Unreached (representative, vertex) pairs after D rounds of R <- min(1, R + R A).
        R = np.zeros((len(reps), N), dtype=np.float32)
        R[rep_idx, reps] = 1.0
        for _ in range(D):
            R = np.minimum(R + R @ A, 1.0)
        return int(R.size - np.count_nonzero(R))

    def dup_count(darts):
        seen = set()
        dup = 0
        for i, j, s in darts:
            key = (i, j, s)
            if key in seen:
                dup += 1
            seen.add(key)
        return dup

    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, p[i], rng.randrange(G)] for p in layers for i in range(k)]
    perms = [perm_for(s) for _, _, s in darts]
    cur = reach_cost(build_A(darts, perms)) + _PENALTY * dup_count(darts)

    for t in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_pm = perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = perm_for(new_s)
        c2 = reach_cost(build_A(darts, perms)) + _PENALTY * dup_count(darts)
        temp = 3.0 * (1.0 - t / iters) + 0.3
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
        else:
            darts[idx][2] = old_s
            perms[idx] = old_pm

    if cur != 0:
        return None
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + int(pm[g])
            E.add((min(a, b), max(a, b)))
    return N, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
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

    # Main search. Small k is favoured: k = 1 is a bipartite Cayley graph.
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 16 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, 2500)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
