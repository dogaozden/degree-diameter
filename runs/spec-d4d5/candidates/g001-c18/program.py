import random
import time
from math import gcd

import lib


def _moore(d, D):
    """Moore-type upper bound on bipartite order (same formula as lib._moore_bound)."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


_GROUP_CACHE = {}


def _group_keys(N):
    """All semidirect-product keys (m, k, r) with m*k == N, covering metacyclic groups."""
    keys = []
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        if m == 1:
            rs = [0]
        else:
            rs = [r for r in range(1, m) if gcd(r, m) == 1 and pow(r, k, m) == 1]
        for r in rs:
            keys.append((m, k, r))
    return keys


def _table(key):
    """Return (order, T) where T[x][y] = x*y for the group with the given key. Identity is 0."""
    t = _GROUP_CACHE.get(key)
    if t is None:
        if len(_GROUP_CACHE) > 300:
            _GROUP_CACHE.clear()
        m, k, r = key
        order, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, y) for y in range(order)] for x in range(order)]
        t = (order, T)
        _GROUP_CACHE[key] = t
    return t


def _lift(p, N, T, darts):
    """Bi-Cayley-style lift: A(u,x) ~ B(v, x*g) for each dart (u, v, g). Returns (n, adj) or None on duplicate edge."""
    n = 2 * p * N
    adj = [[] for _ in range(n)]
    seen = set()
    for u, v, g in darts:
        ba = u * N
        bb = (p + v) * N
        for x in range(N):
            a = ba + x
            b = bb + T[x][g]
            key = a * n + b
            if key in seen:
                return None
            seen.add(key)
            adj[a].append(b)
            adj[b].append(a)
    return n, adj


def _edges(p, N, T, darts):
    return [(u * N + x, (p + v) * N + T[x][g]) for u, v, g in darts for x in range(N)]


def _score(adj, n, srcs, D):
    """Number of (source, vertex) pairs at distance > D (0 means diameter <= D by group symmetry)."""
    bad = 0
    for s in srcs:
        dist = [-1] * n
        dist[s] = 0
        frontier = [s]
        seen = 1
        depth = 0
        while frontier and depth < D:
            depth += 1
            nxt = []
            for u in frontier:
                for w in adj[u]:
                    if dist[w] < 0:
                        dist[w] = depth
                        nxt.append(w)
            seen += len(nxt)
            frontier = nxt
        bad += n - seen
    return bad


def _search(d, D, seed, deadline):
    rng = random.Random(seed)
    M = _moore(d, D)
    best_n, best = 0, None
    STALE_LIMIT = 400
    while time.monotonic() < deadline:
        options = []
        for p in (1, 2, 3):
            hi = M // (2 * p)
            lo = best_n // (2 * p) + 1
            if lo <= hi and hi >= 1:
                options.append((p, lo, hi))
        if not options:
            break
        p, lo, hi = rng.choice(options)
        N = rng.randint(lo, hi)
        keys = _group_keys(N)
        if not keys:
            continue
        key = rng.choice(keys)
        N, T = _table(key)

        # Regular base: d random permutations give a d-regular bipartite multigraph on p+p vertices.
        darts = []
        for _ in range(d):
            perm = list(range(p))
            rng.shuffle(perm)
            for u in range(p):
                darts.append([u, perm[u], 0])

        built = None
        for _ in range(20):
            for dt in darts:
                dt[2] = rng.randrange(N)
            built = _lift(p, N, T, darts)
            if built is not None:
                break
        if built is None:
            continue

        srcs = [u * N for u in range(p)] + [(p + v) * N for v in range(p)]
        cur_n, cur_adj = built
        cur = _score(cur_adj, cur_n, srcs, D)
        stale = 0
        while cur > 0 and time.monotonic() < deadline and stale < STALE_LIMIT:
            i = rng.randrange(len(darts))
            old = darts[i][2]
            darts[i][2] = rng.randrange(N)
            nb = _lift(p, N, T, darts)
            if nb is None:
                darts[i][2] = old
                stale += 1
                continue
            s = _score(nb[1], nb[0], srcs, D)
            if s <= cur:
                stale = 0 if s < cur else stale + 1
                cur, cur_n, cur_adj = s, nb[0], nb[1]
            else:
                darts[i][2] = old
                stale += 1

        if cur == 0:
            n = 2 * p * N
            if n > best_n:
                edges = _edges(p, N, T, darts)
                if lib.is_valid(n, edges, d, D):
                    best_n, best = n, (n, edges)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 3.0)
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    try:
        res = _search(d, D, seed, deadline)
    except Exception:
        res = None
    if res is not None:
        n, edges = res
        if lib.is_valid(n, edges, d, D):
            return n, edges

    try:
        n, edges = lib.haar_graph(d, range(d))
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return 1, []
