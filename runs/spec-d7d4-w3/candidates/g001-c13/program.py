import math
import random
import time

import lib


def _bfs_reaches_all(adj, src, D, V):
    """True if every one of the V vertices is within distance D of src."""
    seen = bytearray(V)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            for w in adj[u]:
                if not seen[w]:
                    seen[w] = 1
                    nxt.append(w)
        if not nxt:
            break
        cnt += len(nxt)
        if cnt == V:
            return True
        frontier = nxt
    return cnt == V


def _groups_of_order(N):
    """Keys (m, k, r) for groups of order N: cyclic (k=1) or Z_m semidirect Z_k."""
    res = [(N, 1, 0)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                res.append((m, k, r))
    return res


def _table(key, cache):
    """Multiplication table T[g][h] and inverse list for a group key, cached."""
    if key in cache:
        return cache[key]
    m, k, r = key
    if k == 1:
        N, mul, inv = lib.cyclic_group(m)
    else:
        N, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(g, h) for h in range(N)] for g in range(N)]
    invl = [inv(h) for h in range(N)]
    if len(cache) > 30:
        cache.clear()
    cache[key] = (N, T, invl)
    return cache[key]


def _try(N, T, invl, S, D):
    """Bi-Cayley graph: a_g ~ b_{g*s} for s in S. Vertex-transitive on each side,
    so diameter <= D iff both a_e and b_e reach all vertices within D."""
    V = 2 * N
    adj = [None] * V
    for g in range(N):
        Tg = T[g]
        adj[g] = [N + Tg[s] for s in S]
    invS = [invl[s] for s in S]
    for x in range(N):
        Tx = T[x]
        adj[N + x] = [Tx[t] for t in invS]
    return _bfs_reaches_all(adj, 0, D, V) and _bfs_reaches_all(adj, N, D, V)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 8.0))
    deadline = start + budget

    q = d - 1
    if D == 3 and d >= 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    # Safe fallback: complete bipartite K_{d,d} (valid for D >= 2).
    fb_n = 2 * d
    fb_edges = [(i, d + j) for i in range(d) for j in range(d)]
    if not lib.is_valid(fb_n, fb_edges, d, D):
        fb_n, fb_edges = 2, [(0, 1)]
        if not lib.is_valid(fb_n, fb_edges, d, D):
            return 1, []

    best_N = d
    best_edges = fb_edges
    cap_N = max(d, lib.moore_bound(d, D) // 2)
    rng = random.Random(seed)
    gcache = {}
    tcache = {}

    try:
        while time.monotonic() < deadline and best_N < cap_N:
            progressed = False
            for N in range(best_N + 1, min(best_N + 6, cap_N) + 1):
                if time.monotonic() >= deadline:
                    break
                if N not in gcache:
                    gcache[N] = _groups_of_order(N)
                groups = gcache[N]
                for _ in range(40):
                    if time.monotonic() >= deadline:
                        break
                    key = rng.choice(groups)
                    NN, T, invl = _table(key, tcache)
                    if NN < d:
                        continue
                    S = [0] + rng.sample(range(1, NN), d - 1)
                    if _try(NN, T, invl, S, D):
                        best_edges = [(g, NN + T[g][s]) for g in range(NN) for s in S]
                        best_N = NN
                        progressed = True
                        break
                if progressed:
                    break
    except Exception:
        pass

    n = 2 * best_N
    if best_N == d:
        return fb_n, fb_edges
    if lib.is_valid(n, best_edges, d, D):
        return n, best_edges
    return fb_n, fb_edges
