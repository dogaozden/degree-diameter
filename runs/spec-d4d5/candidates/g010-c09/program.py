import math
import random
import time

import lib


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over a single group G (one vertex per side per group element).
#
# Vertices A_g = g and B_h = G + h. Connection set S (|S| = d, distinct elements):
# A_g is joined to B_{g*s} for every s in S. Left multiplication is an automorphism,
# so distances from A_e and B_e alone decide the diameter. The graph is bipartite,
# d-regular, and has 2G vertices. This is a different family from the multi-layer
# voltage lifts: the search is a hill-climb on S over many small group tables.
# ----------------------------------------------------------------------------

def _specs(G, rng, limit):
    """Specifications (m, k, r) of semidirect products Z_m x| Z_k with order G, shuffled and capped."""
    cands = [(G, 1, 1)]  # cyclic group
    for k in range(2, G):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        cands.extend((m, k, r) for r in rs[:2])
    rng.shuffle(cands)
    return cands[:limit]


def _table(spec):
    """Multiplication table T[x][y] and inverse list for the group given by spec."""
    m, k, r = spec
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, y) for y in range(order)] for x in range(order)]
    iv = [inv(x) for x in range(order)]
    return T, iv


def _unreached(G, TS, TI, src, D):
    """Number of vertices of the 2G-vertex graph not within distance D of src."""
    N = 2 * G
    seen = bytearray(N)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for x in frontier:
            row = TS[x] if x < G else TI[x - G]
            for y in row:
                if not seen[y]:
                    seen[y] = 1
                    nxt.append(y)
        if not nxt:
            break
        cnt += len(nxt)
        frontier = nxt
    return N - cnt


def _cost(G, T, iv, S, D):
    """Count of (representative, vertex) pairs at distance > D. Zero means diameter <= D."""
    Si = [iv[s] for s in S]
    TS = [[G + row[s] for s in S] for row in T]   # neighbours of A_g
    TI = [[row[t] for t in Si] for row in T]      # neighbours of B_h
    return _unreached(G, TS, TI, 0, D) + _unreached(G, TS, TI, G, D)


def _climb(G, T, iv, d, D, rng, iters, deadline):
    """Hill-climb a connection set S of size d in the group; returns S with cost 0, or None."""
    if G < d:
        return None
    S = rng.sample(range(G), d)
    c = _cost(G, T, iv, S, D)
    best_c = c
    stall = 0
    for it in range(iters):
        if c == 0:
            return S
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _cost(G, T, iv, S2, D)
        if c2 <= c or rng.random() < 0.02:
            S, c = S2, c2
        if c < best_c:
            best_c = c
            stall = 0
        else:
            stall += 1
            if stall > 400:
                break
    return S if c == 0 else None


def _edges_of(G, T, S):
    """Edge list of the bi-Cayley graph: A_g joined to B_{g*s} for s in S."""
    return [(g, G + T[g][s]) for g in range(G) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2 and valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        # K_{d,d} is optimal for diameter 2 among bipartite graphs with max degree d.
        return best

    # Projective plane baseline (strong for D = 3, d-1 a prime power).
    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Main search: bi-Cayley graphs over semidirect products, scanned upward in group order
    # from the current best. Each order gets a time slice split across its candidate groups.
    M = _moore(d, D)
    G = max(best_n // 2 + 1, M // 4, d)
    cap = max(G, M // 2)
    while G <= cap and time.monotonic() < deadline:
        G = max(G, best_n // 2 + 1)
        if G > cap:
            break
        specs = _specs(G, rng, 6)
        if not specs:
            G += 1
            continue
        now = time.monotonic()
        slice_total = max(0.0, deadline - now) / (cap - G + 1)
        per = slice_total / len(specs)
        for spec in specs:
            if time.monotonic() >= deadline:
                break
            T, iv = _table(spec)
            S = _climb(G, T, iv, d, D, rng, 3000, time.monotonic() + per)
            if S is not None:
                consider(2 * G, _edges_of(G, T, S))
                break
        G += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
