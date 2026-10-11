"""Bi-Cayley (Haar-type) search for bipartite graphs of max degree d and diameter D.

Construction: for a group G of order n, vertices A_x and B_y (x, y in G) with
A_x adjacent to B_{x*s} for every s in a connection set S of size d. Left
multiplication is an automorphism that is transitive on each side, so the
diameter is exact after two BFS runs (from A_identity and B_identity). Groups
are cyclic or semidirect products Z_m x| Z_k. S is found by annealing on the
number of unreached pairs. Orders grow upward from the best valid graph so far.

Fallbacks: K_{d,d}, PG(2,q) incidence, and the Araujo-Pardo-Lopez graph. Every
candidate passes lib.is_valid before it is kept.
"""
import math
import random
import time

import lib


def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _sample_group(G, rng):
    """Return (table, inv) for a random group of order G, with table[x][y] = x*y and identity 0."""
    if G < 2:
        return None
    for _ in range(40):
        if rng.random() < 0.3:
            k = 1
        else:
            divs = [j for j in range(2, G) if G % j == 0 and G // j >= 2]
            k = rng.choice(divs) if divs else 1
        if k == 1:
            tbl = [[(x + y) % G for y in range(G)] for x in range(G)]
        else:
            m = G // k
            cands = []
            for _ in range(60):
                r = rng.randrange(1, m)
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    cands.append(r)
            if not cands:
                continue
            r = rng.choice(cands)
            try:
                _, mul, _ = lib.semidirect_group(m, k, r)
            except ValueError:
                continue
            tbl = [[mul(x, y) for y in range(G)] for x in range(G)]
        inv = [0] * G
        for x in range(G):
            row = tbl[x]
            for y in range(G):
                if row[y] == 0:
                    inv[x] = y
                    break
        return tbl, inv
    return None


def _reach(tbl, S, Sinv, G, D, src):
    """Number of vertices within distance D of src in the bi-Cayley graph (A_x = x, B_y = G + y)."""
    seen = bytearray(2 * G)
    seen[src] = 1
    frontier = [src]
    count = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < G:
                row = tbl[u]
                for s in S:
                    v = G + row[s]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                row = tbl[u - G]
                for si in Sinv:
                    v = row[si]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        if not nxt:
            break
        count += len(nxt)
        frontier = nxt
    return count


def _cost(tbl, S, Sinv, G, D):
    """Unreached pairs from A_identity and B_identity. Zero means diameter <= D (vertex-transitive on each side)."""
    N = 2 * G
    return (N - _reach(tbl, S, Sinv, G, D, 0)) + (N - _reach(tbl, S, Sinv, G, D, G))


def _search(G, d, D, rng, iters, deadline):
    """Anneal a connection set S of size d in a random group of order G. Returns (tbl, S) or None."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    tbl, inv = g

    def ev(T):
        return _cost(tbl, T, [inv[s] for s in T], G, D)

    S = rng.sample(range(G), d)
    c = ev(S)
    for _ in range(iters):
        if c == 0:
            break
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        T = S[:]
        T[i] = new
        c2 = ev(T)
        if c2 <= c or rng.random() < 0.02:
            S, c = T, c2
    return (tbl, S) if c == 0 else None


def _haar_edges(tbl, S, G):
    E = [(x, G + tbl[x][s]) for x in range(G) for s in S]
    return 2 * G, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Bi-Cayley search: a valid group of order G gives 2G vertices.
    target_G = lib.moore_bound(d, D) // 2
    G = max(d, best_n // 2 + 1)
    fails = 0
    while time.monotonic() < deadline and G <= target_G and fails < 12:
        res = None
        for _ in range(3):
            if time.monotonic() >= deadline:
                break
            res = _search(G, d, D, rng, 600, deadline)
            if res is not None:
                break
        if res is not None:
            tbl, S = res
            n, e = _haar_edges(tbl, S, G)
            consider(n, e)
            fails = 0
        else:
            fails += 1
        G += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
