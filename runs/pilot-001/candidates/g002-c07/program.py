import random
import time
import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d.

    Returns (n, edges) or None. Points are 0..m-1 and lines are m..2m-1.
    """
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _search_m(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D.

    Cost = number of vertex pairs at distance > D. Returns S with cost 0, or None.
    """
    others = list(range(1, m))

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
        if ct <= c:  # accept sideways moves to escape plateaus
            S, c = T, ct
    return S if c == 0 else None


def _extend(best, d, D, deadline, rng):
    """Spare-degree extension: greedily attach new vertex pairs to vertices with spare degree.

    A new pair (a, b) on opposite sides gets the edge a-b, plus random edges from a to spare
    vertices on b's side and from b to spare vertices on a's side. A pair is kept only if the
    whole graph still has diameter <= D (checked with lib.bad_pairs). Bipartiteness is kept
    because every new edge joins opposite sides. Returns (n, edges, side) or None.
    """
    n, edges, side = best[0], list(best[1]), list(best[2])
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    grown = False
    fails = 0
    while time.monotonic() < deadline and fails < 300:
        slackA = [v for v in range(n) if side[v] == 0 and deg[v] < d]
        slackB = [v for v in range(n) if side[v] == 1 and deg[v] < d]
        if not slackA or not slackB:
            break
        ra = rng.randint(0, min(d - 1, len(slackB)))
        rb = rng.randint(0, min(d - 1, len(slackA)))
        nbA = rng.sample(slackB, ra)  # neighbours of new side-0 vertex a
        nbB = rng.sample(slackA, rb)  # neighbours of new side-1 vertex b
        a, b = n, n + 1
        new_edges = [(a, b)] + [(a, x) for x in nbA] + [(b, y) for y in nbB]
        cand = edges + new_edges
        n2 = n + 2
        if lib.bad_pairs(n2, cand, D) == 0:
            edges = cand
            side.extend([0, 1])
            deg.extend([0, 0])
            for u, v in new_edges:
                deg[u] += 1
                deg[v] += 1
            n = n2
            grown = True
            fails = 0
        else:
            fails += 1
    if not grown:
        return None
    return n, edges, side


def build(d, D, seed, time_limit):
    start = time.monotonic()
    search_deadline = start + 0.5 * time_limit
    final_deadline = start + 0.72 * time_limit
    rng = random.Random(seed)

    n0, e0 = lib.haar_graph(d, range(d))  # K_{d,d}
    fallback = (n0, e0, [0] * d + [1] * d)
    best = fallback

    # D = 3: projective plane with the largest prime power q <= d - 1.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            half = pg[0] // 2
            best = (pg[0], pg[1], [0] * half + [1] * half)

    # General D: local search over Haar graphs with growing modulus m.
    if d >= 3 and D >= 2:
        m, misses = d + 1, 0
        while time.monotonic() < search_deadline and misses < 4:
            S = _search_m(d, D, m, rng, search_deadline, 120)
            if S is not None:
                n, edges = lib.haar_graph(m, S)
                if n > best[0]:
                    best = (n, edges, [0] * m + [1] * m)
                misses = 0
            else:
                misses += 1
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback[0], fallback[1]

    # Spare-degree extension of the best graph found.
    ext = _extend(best, d, D, final_deadline, rng)
    if ext is not None and ext[0] > best[0] and lib.is_valid(ext[0], ext[1], d, D):
        return ext[0], ext[1]
    return best[0], best[1]
