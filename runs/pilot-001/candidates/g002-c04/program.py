import random
import time
import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (degree q + 1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _cost(m, S, D):
    """Number of vertices of the Haar graph H(Z_m, S) not within distance D of vertex a_0.

    The Haar graph is vertex-transitive (translations on both sides, plus the swap a_i <-> b_{-i}),
    so the diameter is <= D exactly when every vertex is within D of a_0. One BFS on Z_m suffices.
    Vertex a_i is index i; vertex b_j is index m + j.
    """
    dist = [-1] * (2 * m)
    dist[0] = 0
    frontier = [0]
    for step in range(1, D + 1):
        if not frontier:
            break
        nxt = []
        for v in frontier:
            if v < m:
                for s in S:
                    w = m + (v + s) % m
                    if dist[w] < 0:
                        dist[w] = step
                        nxt.append(w)
            else:
                j = v - m
                for s in S:
                    w = (j - s) % m
                    if dist[w] < 0:
                        dist[w] = step
                        nxt.append(w)
        frontier = nxt
    return dist.count(-1)


def _search_m(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D.

    Cost = number of vertices beyond distance D from a_0. Returns S with cost 0, or None.
    """
    others = list(range(1, m))

    S = [0] + rng.sample(others, d - 1)
    c = _cost(m, S, D)
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
        ct = _cost(m, T, D)
        if ct <= c:  # accept sideways moves to escape plateaus
            S, c = T, ct
    return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}
    best = fallback

    # D = 3: projective plane with the largest prime power q <= d - 1 (beats K_{d,d} whenever d-1 is not a prime power).
    if D == 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

    # General D: local search over Haar graphs with growing modulus m, using the fast single-BFS cost.
    if d >= 3 and D >= 2:
        m, misses = d + 1, 0
        while time.monotonic() < deadline and misses < 4:
            S = _search_m(d, D, m, rng, deadline, 400)
            if S is not None:
                n, edges = lib.haar_graph(m, S)
                if n > best[0]:
                    best = (n, edges)
                misses = 0
            else:
                misses += 1
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
