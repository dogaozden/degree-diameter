import math
import random
import time

import numpy as np

import lib


def _bfs_within(adj, src, n, D):
    """True if every vertex is reachable from src within D steps."""
    seen = bytearray(n)
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
        count += len(nxt)
        if count == n:
            return True
        if not nxt:
            return False
        frontier = nxt
    return count == n


def _groups(N, rng):
    """Metacyclic groups Z_m x| Z_k of order N as (m, k, r) triples (cyclic when r = 1, k = 1)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m == 1:
            out.append((1, k, 0))
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        if len(rs) > 6:
            rs = rng.sample(rs, 6)
        out.extend((m, k, r) for r in rs)
    return out


def _group_table(m, k, r):
    """Multiplication table (list of lists) for the group coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d)."""
    N = m * k
    if m == 1:
        pw = np.zeros(k, dtype=np.int64)
    else:
        pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    X = np.arange(N, dtype=np.int64)
    a = X // k
    b = X % k
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    B = (b[:, None] + b[None, :]) % k
    return (A * k + B).tolist()


def _sample(T, N, b, d, D, rng):
    """Random bi-Cayley lift over a base with b vertices per side and d-regular base multigraph.

    Left vertex (i, x) is joined to right vertex (j, x*g) for each dart (i, j, g).
    Left translations act transitively on each fibre, so BFS from one representative
    per fibre (2b BFS runs) decides the diameter.
    Returns the sorted edge list, or None if the diameter exceeds D.
    """
    R = b * N
    adj = [[] for _ in range(2 * R)]
    for _ in range(d):
        perm = list(range(b))
        rng.shuffle(perm)
        for i in range(b):
            j = perm[i]
            g = rng.randrange(N)
            base_r = R + j * N
            for x in range(N):
                L = i * N + x
                Rv = base_r + T[x][g]
                adj[L].append(Rv)
                adj[Rv].append(L)
    for i in range(b):
        if not _bfs_within(adj, i * N, 2 * R, D):
            return None
    for j in range(b):
        if not _bfs_within(adj, R + j * N, 2 * R, D):
            return None
    edges = set()
    for u in range(R):
        for v in adj[u]:
            edges.add((u, v))
    return sorted(edges)


def _fallback(d, D):
    """Always-valid small graph."""
    if d < 1:
        return 1, []
    if D >= 2:
        n = 2 * d
        edges = [(i, d + j) for i in range(d) for j in range(d)]
        if lib.is_valid(n, edges, d, D):
            return n, edges
    if D >= 1:
        if lib.is_valid(2, [(0, 1)], d, D):
            return 2, [(0, 1)]
    return 1, []


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    best_n, best_edges = _fallback(d, D)
    if d < 2 or D < 2:
        return best_n, best_edges

    # Total order is 2*b*N, so b*N <= maxT.
    maxT = lib.moore_bound(d, D) // 2
    groups_by_N = {}
    cache = {}

    while time.monotonic() < deadline:
        best_bN = best_n // 2
        lo = max(best_bN + 1, maxT // 2)
        if lo > maxT:
            break
        b = rng.choice((1, 1, 2, 3))
        nlo = -(-lo // b)
        nhi = maxT // b
        if nlo > nhi:
            continue
        N = rng.randint(nlo, nhi)
        if N not in groups_by_N:
            groups_by_N[N] = _groups(N, rng)
        gs = groups_by_N[N]
        if not gs:
            continue
        key = rng.choice(gs)
        if key not in cache:
            if len(cache) > 20:
                cache.clear()
            cache[key] = _group_table(*key)
        T = cache[key]
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            n = 2 * b * N
            if n <= best_n:
                break
            edges = _sample(T, N, b, d, D, rng)
            if edges is None:
                continue
            if lib.is_valid(n, edges, d, D):
                best_n, best_edges = n, edges
                break

    return best_n, best_edges
