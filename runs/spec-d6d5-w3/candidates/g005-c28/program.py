"""Bi-Cayley group search (bold variant).

Each candidate is a bipartite graph on two sides A and B of size G, where G is
the order of a group (semidirect product Z_m x| Z_k, sampled at random). Vertex
A_g is joined to B_{g*s} for each of d voltages s in a set S. Left multiplication
is an automorphism that is transitive on each side, so validity only needs BFS
from A_e and B_e. Search is greedy construction followed by plateau-tolerant
local search over the voltage set. Every returned graph passes lib.is_valid.
Fallbacks: K_{d,d}, the projective-plane incidence graph, and the Araujo-Pardo-Lopez
graph where applicable. This program has not been executed here, so
lib.is_valid is the final gate.
"""
import math
import random
import time

import lib


def _fallback_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _fallback_araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _group_tables(m, k, r):
    """Return (G, M, MI) for Z_m x|_r Z_k: M[x][y] = x*y and MI[h][s] = h*s^{-1}."""
    G, mul, inv = lib.semidirect_group(m, k, r)
    M = [[mul(x, y) for y in range(G)] for x in range(G)]
    invs = [inv(y) for y in range(G)]
    MI = [[M[h][invs[s]] for s in range(G)] for h in range(G)]
    return G, M, MI


def _sample_group(G, rng):
    """Random semidirect product of order G, or None if none was found quickly."""
    divs = [k for k in range(1, 13) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    for _ in range(30):
        k = rng.choice(divs)
        m = G // k
        r = 1
        if k > 1 and rng.random() < 0.85:
            cands = [x for x in rng.sample(range(1, m), min(m - 1, 80))
                     if math.gcd(x, m) == 1 and pow(x, k, m) == 1 % m]
            if cands:
                r = rng.choice(cands)
        try:
            return _group_tables(m, k, r)
        except ValueError:
            continue
    return None


def _unreached(G, Sv, M, MI, D, src):
    """Number of vertices not within distance D of src in the bi-Cayley graph."""
    N = 2 * G
    seen = bytearray(N)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < G:
                row = M[u]
                for s in Sv:
                    v = G + row[s]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                row = MI[u - G]
                for s in Sv:
                    v = row[s]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        cnt += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return N - cnt


def _cost(G, Sv, M, MI, D):
    """Unreached count from the two side representatives. Zero means diameter <= D."""
    return _unreached(G, Sv, M, MI, D, 0) + _unreached(G, Sv, M, MI, D, G)


def _search_group(G, M, MI, d, D, rng, deadline, iters=60, cand=30):
    """Greedy voltage construction, then plateau-tolerant local search. Returns S or None."""
    if G < d:
        return None
    while time.monotonic() < deadline:
        S = []
        for _ in range(d):
            bc, bs = None, None
            for s in rng.sample(range(G), min(G, cand + 10)):
                if s in S:
                    continue
                c = _cost(G, S + [s], M, MI, D)
                if bc is None or c < bc:
                    bc, bs = c, s
            if bs is None:
                return None
            S.append(bs)
        cur = _cost(G, S, M, MI, D)
        for _ in range(iters):
            if cur == 0 or time.monotonic() >= deadline:
                break
            i = rng.randrange(d)
            bc, bs = None, None
            for s in rng.sample(range(G), min(G, cand)):
                if s in S:
                    continue
                T = S[:]
                T[i] = s
                c = _cost(G, T, M, MI, D)
                if bc is None or c < bc:
                    bc, bs = c, s
            if bs is not None and bc <= cur:
                S[i] = bs
                cur = bc
        if cur == 0:
            return S
    return None


def _edges(G, S, M):
    """Full graph from a voltage set: n = 2G, A_g ~ B_{g*s}."""
    E = []
    for g in range(G):
        row = M[g]
        for s in S:
            E.append((g, G + row[s]))
    return 2 * G, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 5.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _fallback_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _fallback_araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if best[0] >= lib.moore_bound(d, D):
        return best

    while time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        hi = lo + max(3, lo // 12)
        G = rng.randint(lo, hi)
        g = _sample_group(G, rng)
        if g is None:
            continue
        Gs, M, MI = g
        att_deadline = min(deadline, time.monotonic() + 8.0)
        S = _search_group(Gs, M, MI, d, D, rng, att_deadline)
        if S is not None:
            n, e = _edges(Gs, S, M)
            consider(n, e)
            if best[0] >= lib.moore_bound(d, D):
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
