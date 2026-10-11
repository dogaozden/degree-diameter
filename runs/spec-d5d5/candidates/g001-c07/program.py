import random
import time
from math import gcd

import lib


def _diam_ok(adj, n, D):
    """Check that BFS from A_0 (vertex 0) and B_0 (vertex n//2) reaches every vertex within D steps.

    Left multiplication by group elements is an automorphism that acts transitively on each side,
    so these two sources cover all pairwise distances.
    """
    for src in (0, n // 2):
        dist = [-1] * n
        dist[src] = 0
        frontier = [src]
        seen = 1
        for depth in range(1, D + 1):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if dist[v] < 0:
                        dist[v] = depth
                        nxt.append(v)
            seen += len(nxt)
            frontier = nxt
            if not frontier:
                break
        if seen != n:
            return False
    return True


def _groups(N):
    """All semidirect products Z_m x| Z_k with m*k = N, coded as (m, k, r)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
                continue
            out.append((m, k, r))
    return out


def _search(N, d, D, rng, end):
    """Random bi-Cayley graphs over groups of order N: A_x ~ B_{x*s} for s in S (|S| = d).

    Returns (2N, edges) with diameter <= D, or None if nothing is found before `end`.
    """
    groups = _groups(N)
    if not groups:
        return None
    rng.shuffle(groups)
    gi = 0
    while time.monotonic() < end:
        m, k, r = groups[gi % len(groups)]
        gi += 1
        _, mul, _ = lib.semidirect_group(m, k, r)
        mt = [[mul(x, y) for y in range(N)] for x in range(N)]
        for _ in range(200):
            if time.monotonic() >= end:
                return None
            S = rng.sample(range(N), d)
            adj = [[] for _ in range(2 * N)]
            for x in range(N):
                row = mt[x]
                for s in S:
                    y = N + row[s]
                    adj[x].append(y)
                    adj[y].append(x)
            if _diam_ok(adj, 2 * N, D):
                edges = [(x, v) for x in range(N) for v in adj[x]]
                return 2 * N, edges
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.8 * time_limit

    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    # Fallback: K_{d,d}, always valid.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    rng = random.Random(seed)
    # Grow the group order one step at a time from the current best.
    while time.monotonic() < deadline:
        N = best_n // 2 + 1
        res = _search(N, d, D, rng, deadline)
        if res is None:
            break
        n, edges = res
        if n > best_n and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_n = n
    return best
