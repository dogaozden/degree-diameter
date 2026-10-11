"""Bold reconstruction: single-base Haar graphs over non-abelian groups.

For a finite group G and a connection set S of size d, the Haar graph H(G, S) has
parts A = {a_g} and B = {b_h} with a_g ~ b_{gs} for s in S. It is d-regular and
bipartite on 2|G| vertices. Left multiplication by G is an automorphism group that
is transitive on each part, so diameter <= D holds iff the balls of radius D around
a_e and b_e both cover the whole graph. That makes the check two BFS runs.

The search climbs |G| upward through a ladder of group orders. For each order it
tries several groups (cyclic, semidirect Z_m x| Z_k, direct products, and the
Heisenberg group of order p^3) and hill-climbs S with annealed acceptance. Every
accepted graph is verified with lib.is_valid. A K_{d,d} fallback (and, for D = 3,
the projective-plane and Araujo-Pardo-Lopez graphs) guarantees a valid output.
"""
import math
import random
import time

import lib


def _is_prime(q):
    if q < 2:
        return False
    i = 2
    while i * i <= q:
        if q % i == 0:
            return False
        i += 1
    return True


def _table_from(order, mul, inv):
    mt = [[mul(x, y) for y in range(order)] for x in range(order)]
    iv = [inv(x) for x in range(order)]
    return mt, iv


def _table_heisenberg(p):
    """Heisenberg group of order p^3; element (x, y, z) is coded as x*p*p + y*p + z."""
    coords = [(x, y, z) for x in range(p) for y in range(p) for z in range(p)]
    G = len(coords)
    mt = [[0] * G for _ in range(G)]
    iv = [0] * G
    for i, (x1, y1, z1) in enumerate(coords):
        row = mt[i]
        for j, (x2, y2, z2) in enumerate(coords):
            row[j] = ((x1 + x2) % p) * p * p + ((y1 + y2) % p) * p + (z1 + z2 + x1 * y2) % p
        iv[i] = ((-x1) % p) * p * p + ((-y1) % p) * p + (x1 * y1 - z1) % p
    return mt, iv


def _group_candidates(G, rng, cap):
    cands = []
    p = round(G ** (1.0 / 3.0))
    for q in (p - 1, p, p + 1):
        if q >= 2 and q ** 3 == G and _is_prime(q):
            cands.append(("heis", q))
    for k in range(1, 13):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        rs = [1]
        if k > 1:
            units = [r for r in range(2, m)
                     if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            rng.shuffle(units)
            rs += units[:3]
        for r in rs:
            cands.append(("sd", m, k, r))
    rng.shuffle(cands)
    return cands[:cap]


def _make_group(c, G):
    """Return (mt, iv) multiplication and inverse tables for the group described by c."""
    if c[0] == "heis":
        mt, iv = _table_heisenberg(c[1])
        if len(mt) != G:
            raise ValueError("order mismatch")
        return mt, iv
    _, m, k, r = c
    order, mul, inv = lib.semidirect_group(m, k, r)
    if order != G:
        raise ValueError("order mismatch")
    return _table_from(order, mul, inv)


def _haar_adj(G, mt, iv, S):
    adj = [None] * (2 * G)
    sinv = [iv[s] for s in S]
    for g in range(G):
        row = mt[g]
        adj[g] = [G + row[s] for s in S]
    for h in range(G):
        row = mt[h]
        adj[G + h] = [row[t] for t in sinv]
    return adj


def _reach(adj, src, D, n):
    seen = bytearray(n)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = 1
                    nxt.append(v)
        if not nxt:
            break
        cnt += len(nxt)
        frontier = nxt
    return cnt


def _haar_cost(G, mt, iv, S, D):
    """Number of (source, vertex) pairs unreached from a_e and b_e within D. Zero iff valid."""
    n = 2 * G
    adj = _haar_adj(G, mt, iv, S)
    return (n - _reach(adj, 0, D, n)) + (n - _reach(adj, G, D, n))


def _haar_edges(G, mt, S):
    E = []
    for g in range(G):
        row = mt[g]
        for s in S:
            E.append((g, G + row[s]))
    return 2 * G, E


def _search_group(G, mt, iv, d, D, rng, deadline, iters):
    S = rng.sample(range(G), d)
    cur = _haar_cost(G, mt, iv, S, D)
    T = 1.0
    for _ in range(iters):
        if cur == 0:
            return S
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T2 = S[:]
        T2[i] = x
        c = _haar_cost(G, mt, iv, T2, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            S, cur = T2, c
        T = max(0.2, T * 0.998)
    return S if cur == 0 else None


def _attempt(G, d, D, rng, end):
    """Try several groups of order G; return a verified (n, edges) or None."""
    for c in _group_candidates(G, rng, 6):
        now = time.monotonic()
        if now >= end:
            break
        try:
            mt, iv = _make_group(c, G)
        except ValueError:
            continue
        gend = min(end, now + 1.5)
        while time.monotonic() < gend:
            S = _search_group(G, mt, iv, d, D, rng, gend, 300)
            if S is not None:
                n, E = _haar_edges(G, mt, S)
                if lib.is_valid(n, E, d, D):
                    return n, E
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    moore = lib._moore_bound(d, D)

    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                consider(*lib.araujo_lopez_graph(q))
            except ValueError:
                pass

    # Ladder over group orders G: vertices = 2G, degree d, diameter D.
    best_G = d
    step = 1
    while time.monotonic() < deadline:
        G = best_G + step
        if 2 * G > moore:
            if step == 1:
                break
            step = 1
            continue
        att_end = min(deadline, time.monotonic() + 3.0)
        res = _attempt(G, d, D, rng, att_end)
        if res is not None:
            best_G = G
            consider(*res)
            step = max(1, G // 40)
        elif step > 1:
            step //= 2

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
