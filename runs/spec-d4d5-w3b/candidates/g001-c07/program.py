import math
import random
import time

import lib

_GROUP_CACHE = {}


def _fallback(d, D):
    """A small graph that is always valid: K_{d,d} for D >= 2, else a single edge."""
    options = []
    if D >= 2:
        options.append(lib.haar_graph(d, range(d)))
    options.append((2, [(0, 1)]))
    for n, edges in options:
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return 1, []


def _groups_of(N):
    """Semidirect products Z_m x| Z_k of order N, coded as (m, k, r)."""
    if N not in _GROUP_CACHE:
        res = []
        for k in range(1, N + 1):
            if N % k:
                continue
            m = N // k
            for r in range(m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    res.append((m, k, r))
        _GROUP_CACHE[N] = res
    return _GROUP_CACHE[N]


def _trial(rng, d, D, p, N, steps, deadline):
    """Hill-climb voltages for a random d-regular bipartite base on p+p vertices lifted over a random group of order N.

    Vertices are A(i,x) = i*N + x and B(j,y) = p*N + j*N + y. Dart (i, j, g) joins A(i,x) to B(j, x*g).
    Left translation is an automorphism, so each base vertex has the same eccentricity at every lift point.
    Checking the 2p representatives A(i,e), B(j,e) therefore certifies diameter <= D.
    Returns the edge list if a valid lift is found, otherwise None.
    """
    m, k, r = rng.choice(_groups_of(N))
    _, mul, _ = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]

    stA = [i for i in range(p) for _ in range(d)]
    stB = stA[:]
    rng.shuffle(stB)
    counts = {}
    for i, j in zip(stA, stB):
        counts[(i, j)] = counts.get((i, j), 0) + 1
    plist = list(counts.items())  # [((i, j), multiplicity)]
    volt = [rng.sample(range(N), c) for _, c in plist]  # distinct voltages per base pair

    nv = 2 * p * N
    reps = [i * N for i in range(p)] + [p * N + j * N for j in range(p)]

    def adjacency():
        adj = [[] for _ in range(nv)]
        for idx, ((i, j), _) in enumerate(plist):
            boff = p * N + j * N
            for g in volt[idx]:
                for x in range(N):
                    a = i * N + x
                    b = boff + T[x][g]
                    adj[a].append(b)
                    adj[b].append(a)
        return adj

    def cost(adj):
        """Number of (representative, vertex) pairs not reached within distance D."""
        tot = 0
        for s in reps:
            seen = bytearray(nv)
            seen[s] = 1
            frontier = [s]
            reached = 1
            for _ in range(D):
                nxt = []
                for u in frontier:
                    for v in adj[u]:
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                if not nxt:
                    break
                reached += len(nxt)
                frontier = nxt
            tot += nv - reached
        return tot

    cur = cost(adjacency())
    for _ in range(steps):
        if cur == 0 or time.monotonic() >= deadline:
            break
        idx = rng.randrange(len(plist))
        vl = volt[idx]
        if len(vl) >= N:
            continue
        t = rng.randrange(len(vl))
        old = vl[t]
        new = rng.randrange(N)
        while new in vl:
            new = rng.randrange(N)
        vl[t] = new
        c2 = cost(adjacency())
        if c2 <= cur:
            cur = c2
        else:
            vl[t] = old

    if cur != 0:
        return None
    edges = []
    for idx, ((i, j), _) in enumerate(plist):
        boff = p * N + j * N
        for g in volt[idx]:
            for x in range(N):
                edges.append((i * N + x, boff + T[x][g]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.75 * time_limit, time_limit - 3.0))

    best = _fallback(d, D)

    # Optimal D = 3 case: projective plane incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, edges = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, edges, d, D):
            return n, edges

    moore = lib.moore_bound(d, D)
    rng = random.Random(seed)
    best_n = best[0]
    budget = 1
    steps = 400

    while time.monotonic() < deadline and best_n < moore:
        for n in range(2, moore + 1, 2):
            if time.monotonic() >= deadline:
                break
            if n <= best_n:
                continue
            half = n // 2
            opts = [p for p in range(1, min(half, 8) + 1)
                    if half % p == 0 and max(d, 2) <= half // p <= 400]
            if not opts:
                continue
            for _ in range(budget):
                if time.monotonic() >= deadline:
                    break
                p = rng.choice(opts)
                N = half // p
                edges = _trial(rng, d, D, p, N, steps, deadline)
                if edges is not None and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_n = n
                    break
        budget *= 2

    return best
