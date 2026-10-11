import math
import random
import time

import lib


# Bold family for D >= 4: Haar graphs H(G, S) of finite groups G.
# Parts A = {A_g} and B = {B_g}; A_g ~ B_{g*s} for s in S with |S| = d.
# Left multiplication by x is an automorphism (A_g -> A_{xg}, B_g -> B_{xg}), so
# validity reduces to two BFS runs: one from A_e and one from B_e, each reaching
# all 2|G| vertices within distance D. This makes candidate evaluation very cheap.
#
# D = 3 keeps the projective-plane / Araujo-Pardo-Lopez constructions.
# K_{d,d} is the fallback and is always kept if nothing better validates.


def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _options(N):
    """Metacyclic groups Z_a x|_r Z_b of order N as (a, b, r); r = 1 gives direct products."""
    opts = [(N, 1, 1)]  # cyclic group
    for b in range(2, N + 1):
        if N % b:
            continue
        a = N // b
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a:
                opts.append((a, b, r))
    return opts


def _table(a, b, r):
    """Multiplication table M[x][y] of Z_a x|_r Z_b; element (u, v) is coded as u*b + v."""
    N = a * b
    pw = [pow(r, t, a) for t in range(b)]
    coords = [divmod(x, b) for x in range(N)]
    M = []
    for u1, v1 in coords:
        p = pw[v1]
        M.append([((u1 + p * u2) % a) * b + (v1 + v2) % b for u2, v2 in coords])
    _, _, inv = lib.semidirect_group(a, b, r)
    iv = [inv(x) for x in range(N)]
    return N, M, iv


def _adjacency(N, M, iv, S):
    """Adjacency lists of H(G, S): vertex g is A_g, vertex N + h is B_h."""
    ivS = [iv[s] for s in S]
    adj = [None] * (2 * N)
    for g in range(N):
        row = M[g]
        adj[g] = [N + row[s] for s in S]
        adj[N + g] = [row[t] for t in ivS]
    return adj


def _reached(adj, src, D, total):
    """Number of vertices within distance D of src (including src)."""
    seen = bytearray(total)
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
        if not nxt:
            break
        count += len(nxt)
        frontier = nxt
    return count


def _cost(N, M, iv, S, D):
    """Unreached (source, vertex) pairs from A_e and B_e. Zero means diameter <= D."""
    adj = _adjacency(N, M, iv, S)
    tot = 2 * N
    return (tot - _reached(adj, 0, D, tot)) + (tot - _reached(adj, N, D, tot))


def _search(d, D, N, M, iv, rng, deadline, iters):
    """Hill-climb a d-subset S of the group so that H(G, S) has diameter <= D."""
    cur = rng.sample(range(N), d)
    c = _cost(N, M, iv, cur, D)
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        t = rng.randrange(N)
        if t in cur:
            continue
        new = cur[:]
        new[i] = t
        c2 = _cost(N, M, iv, new, D)
        if c2 <= c or rng.random() < 0.02:
            cur, c = new, c2
    return (cur if c == 0 else None), c


def _haar_edges(N, M, S):
    """Full edge list of H(G, S) with 2N vertices."""
    edges = []
    for g in range(N):
        row = M[g]
        for s in S:
            edges.append((g, N + row[s]))
    return 2 * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if best_n >= lib.moore_bound(d, D):
        return best

    if D == 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
        if best_n >= lib.moore_bound(d, D):
            return best

    # Main search: Haar graphs over metacyclic groups of order N, searching
    # upward from the current best half-order.
    tables = {}
    target = best_n // 2 + 1
    while time.monotonic() < deadline:
        if best_n >= lib.moore_bound(d, D):
            break
        N = target if rng.random() < 0.5 else target + rng.randrange(1, 4)
        if N < d:
            N = d
        opts = _options(N)
        a, b, r = rng.choice(opts)
        key = (a, b, r)
        if key not in tables:
            if len(tables) >= 24:
                tables.clear()
            tables[key] = _table(a, b, r)
        Ng, M, iv = tables[key]
        per = min(deadline, time.monotonic() + 3.0)
        S, _ = _search(d, D, Ng, M, iv, rng, per, 400)
        if S is not None:
            n, e = _haar_edges(Ng, M, S)
            consider(n, e)
            target = max(target, Ng + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
