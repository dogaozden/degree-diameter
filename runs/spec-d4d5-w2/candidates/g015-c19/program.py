import math
import random
import time

import lib

_TABLE_CACHE = {}


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    if d - 1 > 40:
        return None
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _groups_of_order(G):
    """(m, k, r) triples describing semidirect products Z_m x| Z_k of order G."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if k == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _group_tables(m, k, r):
    """Multiplication table and inverse list for the group, cached."""
    key = (m, k, r)
    if key not in _TABLE_CACHE:
        if len(_TABLE_CACHE) > 300:
            _TABLE_CACHE.clear()
        order, mul, inv = lib.semidirect_group(m, k, r)
        mt = [[mul(x, y) for y in range(order)] for x in range(order)]
        invl = [inv(x) for x in range(order)]
        _TABLE_CACHE[key] = (order, mt, invl)
    return _TABLE_CACHE[key]


def _unreached(adj, src, D, N):
    """Number of vertices not within distance D of src."""
    seen = [False] * N
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
        if not nxt:
            break
        cnt += len(nxt)
        frontier = nxt
    return N - cnt


def _cost(G, mt, invl, S, D):
    """Bi-Cayley graph: A_g ~ B_{g s} for s in S. Zero cost means diameter <= D.

    Left multiplication is an automorphism, so BFS from A_1 and B_1 suffices.
    """
    N = 2 * G
    invS = [invl[s] for s in S]
    adj = [None] * N
    for g in range(G):
        row = mt[g]
        adj[g] = [G + row[s] for s in S]
    for h in range(G):
        row = mt[h]
        adj[G + h] = [row[si] for si in invS]
    return _unreached(adj, 0, D, N) + _unreached(adj, G, D, N)


def _search(d, D, G, rng, deadline, iters):
    """Anneal a connection set S (|S| = d, identity included WLOG) over a random group of order G."""
    opts = _groups_of_order(G)
    if not opts or G - 1 < d - 1:
        return None
    m, k, r = rng.choice(opts)
    order, mt, invl = _group_tables(m, k, r)
    others = list(range(1, order))
    S = [0] + rng.sample(others, d - 1)
    c = _cost(order, mt, invl, S, D)
    temp = 1.0
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        outside = [x for x in others if x not in S]
        if not outside:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(outside)
        ct = _cost(order, mt, invl, T, D)
        if ct <= c or rng.random() < math.exp(-(ct - c) / temp):
            S, c = T, ct
        temp = max(0.2, temp * 0.997)
    if c == 0:
        return S, order, mt
    return None


def _bicayley_edges(G, mt, S):
    return 2 * G, [(g, G + mt[g][s]) for g in range(G) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
        q = d - 2
        if 3 <= q <= 30 and lib.is_prime_power(q):
            try:
                consider(*lib.araujo_lopez_graph(q))
            except ValueError:
                pass

    # Main family: bi-Cayley graphs over semidirect products, searched for the
    # largest group order G such that 2G vertices reach diameter D.
    if D >= 2:
        G_max = lib.moore_bound(d, D) // 2
        while time.monotonic() < deadline:
            G_min = best[0] // 2 + 1
            if G_min > G_max:
                break
            if rng.random() < 0.6:
                G = min(G_max, G_min + rng.randrange(0, 3))
            else:
                G = rng.randint(G_min, G_max)
            res = _search(d, D, G, rng, deadline, 1500)
            if res is not None:
                S, order, mt = res
                n, e = _bicayley_edges(order, mt, S)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
