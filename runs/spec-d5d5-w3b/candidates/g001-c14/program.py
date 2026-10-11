import math
import random
import time

import lib

TRIALS_PER_GROUP = 60
MAX_MISSES = 15


def _reaches_all(adj, V, src, D):
    """True if every vertex is within distance D of src (BFS limited to depth D)."""
    dist = [-1] * V
    dist[src] = 0
    frontier = [src]
    seen = 1
    level = 0
    while frontier and level < D:
        level += 1
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if dist[v] < 0:
                    dist[v] = level
                    nxt.append(v)
        seen += len(nxt)
        frontier = nxt
    return seen == V


def _bicayley_ok(N, T, S, D):
    """Bi-Cayley graph on a_x (id x) and b_y (id N+y), edges a_x -- b_{x*s} for s in S.

    Left multiplication is an automorphism, so the diameter is at most D exactly when
    the eccentricities of a_e and b_e are at most D.
    """
    V = 2 * N
    adj = [[] for _ in range(V)]
    for s in S:
        col = T[s]
        for x in range(N):
            y = N + col[x]
            adj[x].append(y)
            adj[y].append(x)
    return _reaches_all(adj, V, 0, D) and _reaches_all(adj, V, N, D)


def _groups_of_order(N, rng):
    """Multiplication functions for cyclic Z_N plus some semidirect products Z_m x| Z_k (m*k = N)."""
    groups = [lambda x, y, N=N: (x + y) % N]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        for r in rng.sample(rs, min(3, len(rs))):
            _, mul, _ = lib.semidirect_group(m, k, r)
            groups.append(mul)
    rng.shuffle(groups)
    return groups


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 5.0)
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    cap = lib.moore_bound(d, D) // 2
    N = d + 1
    misses = 0
    while N <= cap and misses < MAX_MISSES and time.monotonic() < deadline:
        found = None
        for mul in _groups_of_order(N, rng):
            if found is not None or time.monotonic() >= deadline:
                break
            T = [[mul(x, s) for x in range(N)] for s in range(N)]
            for _ in range(TRIALS_PER_GROUP):
                if time.monotonic() >= deadline:
                    break
                S = rng.sample(range(N), d)
                if _bicayley_ok(N, T, S, D):
                    edges = [(x, N + T[s][x]) for s in S for x in range(N)]
                    if lib.is_valid(2 * N, edges, d, D):
                        found = (2 * N, edges)
                        break
        if found is not None:
            best = found
            misses = 0
        else:
            misses += 1
        N += 1
    return best
