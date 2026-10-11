import math
import random
import time

import lib


def _parent(d, D, seed, deadline):
    """Cyclic Haar-graph search (the parent's method). Used as a guaranteed-valid baseline."""
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def _group_params(N):
    """All (m, k, r) giving a semidirect product Z_m x| Z_k of order N = m*k (k=1 is cyclic)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(1, m + 1):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(m, k, r):
    """Multiplication table and inverse list for the group Z_m x| Z_k."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    tbl = [[mul(x, y) for y in range(order)] for x in range(order)]
    invs = [inv(x) for x in range(order)]
    return tbl, invs


def _bfs_ok(adj, total, D, src):
    """True if BFS from src reaches all `total` vertices within D steps."""
    dist = [-1] * total
    dist[src] = 0
    frontier = [src]
    reached = 1
    level = 0
    while frontier and level < D:
        level += 1
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if dist[v] < 0:
                    dist[v] = level
                    nxt.append(v)
        reached += len(nxt)
        frontier = nxt
    return reached == total


def _search_bicayley(d, D, N, rng, end, cache, params):
    """Random search for a bi-Cayley graph over a group of order N.

    A-vertex x is joined to B-vertex x*s for s in S. Left multiplication is an
    automorphism that is transitive on each side, so BFS from A0 and B0 suffices.
    Identity is always in S (WLOG, by relabelling B).
    """
    if not params:
        return None
    while time.monotonic() < end:
        key = params[rng.randrange(len(params))]
        if key not in cache:
            cache[key] = _table(*key)
        tbl, invs = cache[key]
        S = [0] + rng.sample(range(1, N), d - 1)
        adj = [[N + tbl[x][s] for s in S] for x in range(N)]
        adj += [[tbl[y][invs[s]] for s in S] for y in range(N)]
        if _bfs_ok(adj, 2 * N, D, 0) and _bfs_ok(adj, 2 * N, D, N):
            edges = [(x, N + tbl[x][s]) for x in range(N) for s in S]
            return 2 * N, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = min(0.85 * time_limit, time_limit - 5.0)
    deadline = start + total

    # Calibration case with a known optimal construction.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Safe baseline (always valid).
    baseline = _parent(d, D, seed, start + 0.1 * total)

    # Target case: non-abelian bi-Cayley graphs over semidirect products.
    if not (d == 4 and D == 5):
        return baseline

    best = baseline
    rng = random.Random(seed)
    n_min = 40
    n_max = min(121, lib._moore_bound(d, D) // 2)
    cache = {}
    for N in range(n_min, n_max + 1):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (n_max - N + 1)
        res = _search_bicayley(d, D, N, rng, now + share, cache, _group_params(N))
        if res is not None:
            n, edges = res
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
    return best
