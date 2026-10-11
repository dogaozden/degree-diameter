import math
import random
import time

import lib

# Idea: bi-Cayley (Haar-type) graphs over a finite group G. Vertices are a_x and b_y
# (x, y in G), and a_x ~ b_{x*s} for s in S, |S| = d. Left multiplication is an
# automorphism that is transitive on each side, so diameter <= D reduces to two BFS
# runs, from a_e and from b_e. Connection sets are annealed to minimise the number of
# unreached vertices, over many groups of order G (cyclic and Z_m x| Z_k), and G is
# raised while success continues.


def _pg_fallback(d):
    """Incidence graph of PG(2, q), q + 1 <= d, for the largest prime power q (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _reach_gap(G, S, Sinv, Mt, D, s0):
    """Number of vertices NOT within distance D of the start vertex s0 (A-side if s0 < G)."""
    seen = bytearray(2 * G)
    seen[s0] = 1
    frontier = [s0]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < G:
                row = Mt[u]
                for s in S:
                    v = G + row[s]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                row = Mt[u - G]
                for si in Sinv:
                    v = row[si]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        if not nxt:
            break
        cnt += len(nxt)
        frontier = nxt
    return 2 * G - cnt


def _cost(G, S, Mt, Inv, D):
    Sinv = [Inv[s] for s in S]
    return _reach_gap(G, S, Sinv, Mt, D, 0) + _reach_gap(G, S, Sinv, Mt, D, G)


def _groups_for_order(G, rng):
    """Candidate (m, k, r) with Z_m x|_r Z_k of order G (r = 1 is excluded except for cyclic)."""
    cands = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if k == 1:
            cands.append((m, 1, 1))
            continue
        if m == 1:
            cands.append((1, k, 0))
            continue
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if len(rs) > 8:
            rs = rng.sample(rs, 8)
        for r in rs:
            cands.append((m, k, r))
    return cands


def _tables(G, cand):
    m, k, r = cand
    order, mul, inv = lib.semidirect_group(m, k, r)
    if order != G:
        raise ValueError("order mismatch")
    Mt = [[mul(x, y) for y in range(G)] for x in range(G)]
    Inv = [inv(x) for x in range(G)]
    return Mt, Inv


def _anneal(G, d, D, Mt, Inv, rng, steps, deadline):
    """Anneal a connection set S (|S| = d) until the bi-Cayley graph has diameter <= D."""
    S = rng.sample(range(G), d)
    cur = _cost(G, S, Mt, Inv, D)
    for it in range(steps):
        if cur == 0:
            return S
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c = _cost(G, S, Mt, Inv, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / 0.6):
            cur = c
        else:
            S[i] = old
    return S if cur == 0 else None


def _edges(G, S, Mt):
    E = []
    for x in range(G):
        row = Mt[x]
        for s in S:
            E.append((x, G + row[s]))
    return 2 * G, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Bi-Cayley search: group order G gives 2G vertices.
    target = max(d, best_n // 2 + 1)
    while time.monotonic() < deadline:
        G = target
        cands = _groups_for_order(G, rng)
        if not cands:
            target += 1
            continue
        cand = rng.choice(cands)
        try:
            Mt, Inv = _tables(G, cand)
        except ValueError:
            continue
        S = _anneal(G, d, D, Mt, Inv, rng, 1500, deadline)
        if S is not None:
            n, e = _edges(G, S, Mt)
            consider(n, e)
            target = G + 1

    n, e = best
    if lib.is_valid(n, e, d, D):
        return n, e
    return lib.haar_graph(d, range(d))
