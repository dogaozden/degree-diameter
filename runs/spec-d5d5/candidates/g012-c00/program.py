import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured baselines (always valid, used as the safe fallback).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q); diameter 4, degree q+1."""
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction: annealed random d-regular bipartite graphs.
#
# A graph on K+K vertices (A = 0..K-1, B = K..2K-1) is kept d-regular and
# bipartite by double edge swaps: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).
# The cost is the number of unordered vertex pairs at distance > D.
# Annealing drives the cost to zero, starting from a random regular graph,
# with no group structure assumed.
# ----------------------------------------------------------------------------

def _random_regular(K, d, rng):
    """Random d-regular bipartite graph on K+K vertices as neighbour sets, or None."""
    for _ in range(100):
        S = [set() for _ in range(2 * K)]
        ok = True
        for _layer in range(d):
            placed = False
            for _t in range(200):
                p = list(range(K))
                rng.shuffle(p)
                if all(K + p[i] not in S[i] for i in range(K)):
                    for i in range(K):
                        S[i].add(K + p[i])
                        S[K + p[i]].add(i)
                    placed = True
                    break
            if not placed:
                ok = False
                break
        if ok:
            return S
    return None


def _bad_pairs(n, S, D):
    """Number of unordered vertex pairs at distance > D (bitset ball expansion)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in S[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal(n2, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph on n2 = 2K vertices to diameter <= D; (n, edges) or None."""
    K = n2 // 2
    S = _random_regular(K, d, rng)
    if S is None:
        return None
    E = [(a, b) for a in range(K) for b in S[a]]
    cost = _bad_pairs(2 * K, S, D)
    T0, T1 = 2.0, 0.05
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)

    while cost > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t_start) / span
        T = T0 * (T1 / T0) ** min(1.0, frac)
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or b2 in S[a1] or b1 in S[a2]:
            continue
        S[a1].remove(b1)
        S[b1].remove(a1)
        S[a2].remove(b2)
        S[b2].remove(a2)
        S[a1].add(b2)
        S[b2].add(a1)
        S[a2].add(b1)
        S[b1].add(a2)
        c2 = _bad_pairs(2 * K, S, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            E[i] = (a1, b2)
            E[j] = (a2, b1)
        else:
            S[a1].remove(b2)
            S[b2].remove(a1)
            S[a2].remove(b1)
            S[b1].remove(a2)
            S[a1].add(b1)
            S[b1].add(a1)
            S[a2].add(b2)
            S[b2].add(a2)

    if cost == 0:
        return 2 * K, [(a, b) for a in range(K) for b in S[a]]
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Cycle C_{2D}: bipartite, 2-regular, diameter D.
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baselines.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: random regular bipartite graphs annealed to diameter D,
    # aiming one vertex-pair above the current best order each time.
    K = best[0] // 2 + 1
    while time.monotonic() < deadline - 0.5 and 2 * K <= moore:
        now = time.monotonic()
        slice_end = min(deadline, now + max(1.0, 0.35 * (deadline - now)))
        res = _anneal(2 * K, d, D, rng, slice_end)
        if res is not None:
            consider(res[0], res[1])
            K += 1
        # On failure, retry the same K from a fresh random start.

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
