import math
import random
import time

import lib

# Cost of a candidate cyclic bi-Cayley lift is the number of (representative, vertex)
# pairs not reached within distance D. A lift over Z_m is translation-invariant, so
# every ordered pair is equivalent to one starting at a representative a_{i,0} or b_{j,0}.
# Only 2k BFS runs are needed, not N. Search moves are voltage re-rolls and
# within-layer swaps of B-targets, both kept as bipartite degree-d permutation layers.

_BIG = 10 ** 9


def _pg_graph(d):
    """Incidence graph of PG(2, d-1) when d-1 is a prime power (diameter 3, Moore-optimal)."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    return None


def _araujo_graph(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _adjacency(k, m, darts):
    """Adjacency lists of the lift. A-vertex i*m+g, B-vertex (k+j)*m+h; dart (i,j,s) joins A_{i,g} to B_{j,g+s}."""
    N = 2 * k * m
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        ai = i * m
        bj = (k + j) * m
        for g in range(m):
            a = ai + g
            b = bj + (g + s) % m
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _dup_free(m, darts):
    """True if no two darts give the same edge set (same (i, j) pair with the same voltage mod m)."""
    seen = set()
    for i, j, s in darts:
        key = (i, j, s % m)
        if key in seen:
            return False
        seen.add(key)
    return True


def _cost(k, m, D, darts, limit=float("inf")):
    """Unreached (representative, vertex) pairs at distance > D. Zero means the lift is valid.

    Returns early with a value above `limit` once the running total exceeds it.
    """
    if not _dup_free(m, darts):
        return _BIG
    adj = _adjacency(k, m, darts)
    N = 2 * k * m
    total = 0
    sources = [i * m for i in range(k)] + [(k + j) * m for j in range(k)]
    for src in sources:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
        if total > limit:
            return total
    return total


def _random_darts(d, k, m, rng):
    """d permutation layers over k+k base vertices, each dart with a random voltage in Z_m."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(m)])
    return darts


def _anneal(d, k, m, D, deadline, rng, darts, T0):
    """Simulated annealing on the cyclic lift. Returns (darts, cost)."""
    cost = _cost(k, m, D, darts)
    T = T0
    while cost > 0 and time.monotonic() < deadline:
        T = max(0.05, T * 0.998)
        limit = cost - T * math.log(1.0 - rng.random())  # Metropolis threshold, drawn up front
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(m)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, m, D, darts, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, m, D, darts, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts, cost


def _lift_edges(k, m, darts):
    """Full edge list of the cyclic lift. A-ids < B-ids, so each pair is already ordered."""
    E = set()
    for i, j, s in darts:
        for g in range(m):
            E.add((i * m + g, (k + j) * m + (g + s) % m))
    return 2 * k * m, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    n0, e0 = lib.haar_graph(d, range(d))
    state = {"n": n0, "e": e0}
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        if n > state["n"] and lib.is_valid(n, e, d, D):
            state["n"], state["e"] = n, e

    if D >= 3:
        pg = _pg_graph(d)
        if pg is not None:
            consider(*pg)
        ar = _araujo_graph(d)
        if ar is not None:
            consider(*ar)

    # Cyclic bi-Cayley ladder: keep trying lifts just above the current best order.
    ks = [1, 2, 2, 3]
    while D >= 3 and state["n"] < moore and time.monotonic() < deadline:
        k = rng.choice(ks)
        base = state["n"] // (2 * k)
        lo = base + 1
        hi = lo + max(2, base // 25)
        m = rng.randint(lo, hi)
        darts = _random_darts(d, k, m, rng)
        att = min(deadline, time.monotonic() + 4.0)
        darts, cost = _anneal(d, k, m, D, att, rng, darts, 1.5)
        if cost == 0:
            n, e = _lift_edges(k, m, darts)
            consider(n, e)

    if not lib.is_valid(state["n"], state["e"], d, D):
        return lib.haar_graph(d, range(d))
    return state["n"], state["e"]
