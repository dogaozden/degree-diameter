import math
import random
import time

import lib

# Bold change for D >= 5: instead of cyclic/bi-Cayley voltage lifts found by
# annealing, search Haar graphs H(Gamma, S) over semidirect products
# Gamma = Z_m x| Z_k. Vertices are (g, 0) and (g, 1) for g in Gamma, and
# (g, 0) ~ (g*s, 1) for s in S with |S| = d. Each side has d-regular adjacency,
# the graph is bipartite by construction, and the only check needed is
# diameter <= D, which is a BFS from the two identity vertices.
# Safe fallbacks: projective-plane incidence graph (D >= 3), Araujo-Pardo-Lopez
# graph (D >= 3), and K_{d,d} (D >= 2). Every candidate is checked with lib.is_valid.


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _araujo_candidate(d):
    """Araujo-Pardo-Lopez graph of degree d = q + 2 when q = d - 2 is a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except Exception:
        return None


def _random_group(G, rng):
    """Return (order, mul_table, inv_list) for a random semidirect product Z_m x| Z_k of order G, or None."""
    ks = [k for k in range(1, 13) if G % k == 0 and G // k >= 2]
    if not ks:
        return None
    k = rng.choice(ks)
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
    M = [[mul(x, y) for y in range(order)] for x in range(order)]
    I = [inv(x) for x in range(order)]
    return order, M, I


def _cost(G, M, I, S, D):
    """Unreached (source, vertex) pairs from (1,0) and (1,1) within distance D. Zero iff valid."""
    N = 2 * G
    adj0 = [[G + M[g][s] for s in S] for g in range(G)]
    adj1 = [[M[h][I[s]] for s in S] for h in range(G)]
    adj = adj0 + adj1
    total = 0
    for src in (0, G):
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
    return total


def _hill(G, M, I, d, D, rng, deadline, restarts=3, iters=300):
    """Hill-climb a d-element connection set S in the group so that H(Gamma, S) has diameter <= D."""
    for _ in range(restarts):
        S = rng.sample(range(G), d)
        c = _cost(G, M, I, S, D)
        for _ in range(iters):
            if c == 0:
                return S
            if time.monotonic() >= deadline:
                return None
            i = rng.randrange(d)
            x = rng.randrange(G)
            if x in S:
                continue
            T = S[:]
            T[i] = x
            ct = _cost(G, M, I, T, D)
            if ct <= c or rng.random() < 0.02:
                S, c = T, ct
        if c == 0:
            return S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo_candidate(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Stop early if already at the Moore bound (e.g. calibration cases).
    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    # Main search: Haar graphs over semidirect products, growing the group order.
    while time.monotonic() < deadline and best_n < moore:
        G = max(d, best_n // 2 + 1 + rng.randint(0, 6))
        g = _random_group(G, rng)
        if g is None:
            continue
        order, M, I = g
        S = _hill(order, M, I, d, D, rng, deadline)
        if S is not None:
            E = [(x, order + M[x][s]) for x in range(order) for s in S]
            consider(2 * order, E)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
