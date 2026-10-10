import random
import time
import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (degree q + 1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _nbrs(m, S):
    """Adjacency lists of the Haar graph H(Z_m, S): a_i ~ b_{i+s}, with a_i = i and b_j = m + j."""
    nbr = [None] * (2 * m)
    for i in range(m):
        nbr[i] = [m + (i + s) % m for s in S]
    for j in range(m):
        nbr[m + j] = [(j - s) % m for s in S]
    return nbr


def _bad_from_a0(m, S, D):
    """Number of vertices at distance > D from a_0 in H(Z_m, S).

    The Haar graph has translations acting transitively on each side and a swap automorphism
    exchanging the sides (a_i -> b_{-i}), so the graph has diameter <= D iff every vertex is
    within distance D of a_0. One BFS therefore gives a zero-cost test for the whole graph.
    """
    nbr = _nbrs(m, S)
    N = 2 * m
    seen = bytearray(N)
    seen[0] = 1
    frontier = [0]
    count = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in nbr[u]:
                if not seen[v]:
                    seen[v] = 1
                    nxt.append(v)
        if not nxt:
            break
        count += len(nxt)
        frontier = nxt
    return N - count


def _search_m(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D.

    Returns S with zero cost, or None.
    """
    others = list(range(1, m))
    S = [0] + rng.sample(others, d - 1)
    c = _bad_from_a0(m, S, D)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        in_S = set(S)
        cand = [x for x in others if x not in in_S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = _bad_from_a0(m, T, D)
        if ct <= c:  # accept sideways moves to escape plateaus
            S, c = T, ct
    return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}
    best = fallback

    # D = 3: projective plane with the largest prime power q <= d - 1.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

    # General D: fast local search over Haar graphs with growing modulus m.
    if d >= 3 and D >= 2:
        bound = lib._moore_bound(d, D)
        m, misses = d + 1, 0
        while time.monotonic() < deadline and 2 * m <= bound and misses < 6:
            S = _search_m(d, D, m, rng, deadline, 400)
            if S is not None:
                n, edges = lib.haar_graph(m, S)
                if n > best[0] and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                misses = 0
            else:
                misses += 1
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
