"""Bi-Cayley lift search over metacyclic groups Z_m x|_r Z_k with fast BFS cost.

This version replaces the layered voltage-lift search with a different construction.
A bi-Cayley graph over a group G has vertices A_g and B_h (g, h in G) and edges
A_g ~ B_{g*s} for s in a connection set S of size d. Left multiplication is an
automorphism that is transitive on each side, so the diameter is at most D exactly
when the BFS from A_e and from B_e reaches every vertex within D steps. Each cost
evaluation is therefore two bipartite BFS passes over G elements, which is much
cheaper than all-pairs bitset checks.

The search samples a group of order G (cyclic, abelian, or metacyclic with r != 1),
runs simulated annealing over S to drive the unreached-vertex count to zero, and
ratchets G upward on success. Every returned graph is checked with lib.is_valid.
Fallbacks are K_{d,d}, the projective plane incidence graph, and the Araujo-Lopez graph.
"""
import math
import random
import time

import numpy as np

import lib


_UNITS_CACHE = {}


def _units(m, k):
    """Units r mod m with r^k = 1 mod m (always contains 1)."""
    key = (m, k)
    if key not in _UNITS_CACHE:
        _UNITS_CACHE[key] = [u for u in range(1, m)
                             if math.gcd(u, m) == 1 and pow(u, k, m) == 1 % m]
    return _UNITS_CACHE[key]


def _divisors_ge2(G):
    return [m for m in range(2, G + 1) if G % m == 0]


def _make_group(m, k, r):
    """Group Z_m x|_r Z_k, element (a, b) coded as a*k + b; identity is index 0."""
    G = m * k
    idx = np.arange(G, dtype=np.int64)
    A = idx // k
    Bq = idx % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    return (G, m, k, A, Bq, pw)


def _sample_group(G, rng):
    ds = _divisors_ge2(G)
    if not ds:
        return None
    m = rng.choice(ds)
    k = G // m
    r = rng.choice(_units(m, k))
    return _make_group(m, k, r)


def _rmul(grp, s):
    """Array g -> g*s over all group elements g."""
    G, m, k, A, Bq, pw = grp
    c, dd = divmod(s, k)
    return ((A + pw[Bq] * c) % m) * k + (Bq + dd) % k


def _rinv(grp, s):
    """Index of s^{-1}: (c, d)^{-1} = (-r^{-d} c, -d), with r^{-d} = r^{k-d}."""
    G, m, k, A, Bq, pw = grp
    c, dd = divmod(s, k)
    ic = (-int(pw[(k - dd) % k]) * c) % m
    return ic * k + (-dd) % k


def _cost(G, Rf, Rb, D):
    """Vertices not within distance D of A_e plus those not within D of B_e."""
    total = 0
    for start in (0, 1):
        vis = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
        vis[start][0] = True
        frontier = np.zeros(1, dtype=np.int64)
        side = start
        for _ in range(D):
            R = Rf if side == 0 else Rb
            cand = np.unique(np.concatenate([r[frontier] for r in R]))
            cand = cand[~vis[1 - side][cand]]
            if cand.size == 0:
                break
            vis[1 - side][cand] = True
            frontier = cand
            side = 1 - side
        total += 2 * G - int(vis[0].sum()) - int(vis[1].sum())
    return total


def _attempt(grp, d, D, rng, deadline, iters):
    """Simulated annealing over the connection set S. Returns S or None."""
    G = grp[0]
    S = rng.sample(range(G), d)
    Rf = [_rmul(grp, s) for s in S]
    Rb = [_rmul(grp, _rinv(grp, s)) for s in S]
    cost = _cost(G, Rf, Rb, D)
    T = 3.0
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        nRf = list(Rf)
        nRb = list(Rb)
        nRf[i] = _rmul(grp, new)
        nRb[i] = _rmul(grp, _rinv(grp, new))
        c2 = _cost(G, nRf, nRb, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            S[i] = new
            Rf, Rb, cost = nRf, nRb, c2
        T = max(0.3, T * 0.9985)
    if cost == 0:
        return S
    return None


def _graph_from(grp, S):
    """Bipartite graph on 2G vertices: A_g = g, B_h = G + h, edges A_g ~ B_{g*s}."""
    G = grp[0]
    edges = []
    for s in S:
        R = _rmul(grp, s)
        edges.extend((g, G + int(R[g])) for g in range(G))
    return 2 * G, edges


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 2.0)
    final = t0 + total
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
            if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
                return best
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            consider(*lib.araujo_lopez_graph(d - 2))
    except Exception:
        pass

    # Search: bi-Cayley graphs over sampled metacyclic groups, ratcheting the order.
    maxG = lib.moore_bound(d, D) // 2
    goal = max(d, best_n // 2 + 1)
    fails = 0
    try:
        while True:
            now = time.monotonic()
            if now > final - 0.5 or best_n >= 2 * maxG:
                break
            G = min(max(goal, d), maxG)
            if G < d:
                break
            grp = _sample_group(G, rng)
            if grp is None:
                break
            deadline = min(final, now + 3.0)
            S = _attempt(grp, d, D, rng, deadline, 4000)
            if S is not None:
                n_, e_ = _graph_from(grp, S)
                consider(n_, e_)
                if best_n >= 2 * G:
                    goal = G + max(1, G // 150)
                    fails = 0
                else:
                    fails += 1
            else:
                fails += 1
                if fails >= 6:
                    goal = max(best_n // 2 + 1, d, goal - max(1, goal // 300))
                    fails = 0
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
