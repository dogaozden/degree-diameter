import math
import random
import time

import lib


def _groups(N):
    """Return (mul, inv) pairs for every cyclic and semidirect group Z_m x| Z_k with m*k = N."""
    out = [lib.cyclic_group(N)[1:]]
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
                continue
            _, mul, inv = lib.semidirect_group(m, k, r)
            out.append((mul, inv))
    return out


def _adjacency(N, mul, inv, S):
    """Adjacency of the Haar-type graph: A-node x ~ B-node mul(x, g) for g in S.

    Nodes 0..N-1 are A-vertices, N..2N-1 are B-vertices (B-vertex N+y).
    """
    ginv = [inv(g) for g in S]
    adj_a = [[N + mul(x, g) for g in S] for x in range(N)]
    adj_b = [[mul(y, gi) for gi in ginv] for y in range(N)]
    return adj_a + adj_b


def _diameter_ok(N, adj, D):
    """Left multiplication is an automorphism, so BFS from one A-vertex and one B-vertex suffices."""
    total = 2 * N
    for src in (0, N):
        seen = [False] * total
        seen[src] = True
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        if cnt != total:
            return False
    return True


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    # Always-valid fallback: K_{d,d} (diameter 1).
    fallback = lib.haar_graph(d, range(d))

    rng = random.Random(seed)
    M = lib.moore_bound(d, D)
    n_hi = min(M // 2, 420)  # Haar graph on 2N vertices; N <= M/2

    # Sweep group orders downward; the first order that yields a valid
    # graph is the largest one found, so return it immediately.
    for N in range(n_hi, d - 1, -1):
        if time.monotonic() >= deadline:
            break
        groups = _groups(N)
        slice_end = min(deadline, time.monotonic() + 0.35)
        while time.monotonic() < slice_end:
            mul, inv = rng.choice(groups)
            S = [0] + rng.sample(range(1, N), d - 1)  # right-translate so 0 is in S
            adj = _adjacency(N, mul, inv, S)
            if _diameter_ok(N, adj, D):
                edges = [(x, N + mul(x, g)) for x in range(N) for g in S]
                if lib.is_valid(2 * N, edges, d, D):
                    return 2 * N, edges
    return fallback
