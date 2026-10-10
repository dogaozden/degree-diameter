import random
import time
import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (degree q + 1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bfs(m, S, src):
    """BFS distances in the Haar graph H(Z_m, S) from vertex src (a_i = i, b_j = m + j)."""
    n = 2 * m
    dist = [-1] * n
    dist[src] = 0
    queue = [src]
    for v in queue:  # list grows while iterating
        dv = dist[v] + 1
        if v < m:
            nbrs = [m + (v + s) % m for s in S]
        else:
            j = v - m
            nbrs = [(j - s) % m for s in S]
        for w in nbrs:
            if dist[w] < 0:
                dist[w] = dv
                queue.append(w)
    return dist


def _cost(m, S, D):
    """Total excess distance over D across all vertex pairs, using Z_m symmetry.

    The rotation i -> i + 1 (on both sides) is an automorphism, so every unordered pair is
    equivalent to a pair with a_0 (all targets) or with b_0 (targets on side B). Cost is 0
    iff the diameter is at most D. Unreachable pairs get penalty 2.
    """
    total = 0
    dist = _bfs(m, S, 0)
    for x in dist:
        if x < 0:
            total += 2
        elif x > D:
            total += x - D
    dist = _bfs(m, S, m)
    for x in dist[m:]:
        if x < 0:
            total += 2
        elif x > D:
            total += x - D
    return total


def _search_m(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D.

    Returns S with cost 0, or None.
    """
    others = list(range(1, m))
    S = [0] + rng.sample(others, d - 1)
    c = _cost(m, S, D)
    for it in range(iters):
        if c == 0:
            return S
        if it % 256 == 0 and time.monotonic() >= deadline:
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
    deadline = start + 0.6 * time_limit
    rng = random.Random(seed)

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}
    best = fallback

    # D = 3: projective plane with the largest prime power q <= d - 1 (beats K_{d,d} whenever d-1 is not a prime power).
    if D == 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

    # General D: fast local search over Haar graphs with growing modulus m.
    if d >= 3 and D >= 2:
        m, misses = d + 1, 0
        while time.monotonic() < deadline and misses < 5:
            S = _search_m(d, D, m, rng, deadline, 2000)
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
