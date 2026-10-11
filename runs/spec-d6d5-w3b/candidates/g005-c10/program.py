import math
import random
import time

import numpy as np

import lib

_BIG = 10 ** 9
_INF = float("inf")


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _translation_table(a, b):
    """Return (G, table) for the abelian group Z_a x Z_b, element x*b + y.

    table[s][g] = g + s in the group.
    """
    G = a * b
    idx = np.arange(G)
    x, y = idx // b, idx % b
    table = []
    for s in range(G):
        s1, t1 = divmod(s, b)
        table.append((((x + s1) % a) * b + (y + t1) % b).tolist())
    return G, table


def _cost(k, G, D, darts, table, limit):
    """Number of (representative, vertex) pairs at distance > D in the lift.

    Returns early with a value above `limit` once the running total exceeds it.
    A repeated dart (i, j, s) would create a duplicate edge, so it costs _BIG.
    """
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    seen_darts = set()
    for i, j, s in darts:
        key = (i, j, s)
        if key in seen_darts:
            return _BIG
        seen_darts.add(key)
        pm = table[s]
        ba, bb = i * G, (k + j) * G
        for g in range(G):
            u, v = ba + g, bb + pm[g]
            adj[u].append(v)
            adj[v].append(u)
    total = 0
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    for src in reps:
        seen = bytearray(N)
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
        total += N - count
        if total > limit:
            return total
    return total


def _anneal(d, D, k, G, table, rng, deadline):
    """Anneal over layered bi-Cayley darts on Z_a x Z_b.

    Each layer L is a permutation perms[L] of the k right vertices, and
    dart (i, perms[L][i], volt[L][i]) is created for every left vertex i.
    Every vertex then has degree d. Returns the darts if cost 0 is reached, else None.
    """
    perms = [rng.sample(range(k), k) for _ in range(d)]
    volt = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]

    def darts():
        return [(i, perms[L][i], volt[L][i]) for L in range(d) for i in range(k)]

    cost = _cost(k, G, D, darts(), table, _INF)
    T = 1.0
    while cost > 0 and time.monotonic() < deadline:
        T = max(0.05, T * 0.998)
        limit = cost - T * math.log(1.0 - rng.random())
        L = rng.randrange(d)
        if k == 1 or rng.random() < 0.7:
            i = rng.randrange(k)
            old = volt[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            volt[L][i] = new
            c2 = _cost(k, G, D, darts(), table, limit)
            if c2 <= limit:
                cost = c2
            else:
                volt[L][i] = old
        else:
            a, b = rng.sample(range(k), 2)
            p = perms[L]
            p[a], p[b] = p[b], p[a]
            c2 = _cost(k, G, D, darts(), table, limit)
            if c2 <= limit:
                cost = c2
            else:
                p[a], p[b] = p[b], p[a]
    return darts() if cost == 0 else None


def _edges(k, G, darts, table):
    """Expand darts into the full lift: 2*k*G vertices, edges (A_i,g, B_j,g+s)."""
    E = []
    for i, j, s in darts:
        pm = table[s]
        for g in range(G):
            E.append((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D == 2:
        return best

    # Bi-Cayley lifts over abelian groups Z_a x Z_b (non-cyclic when a > 1 and b > 1).
    ks = [1, 1, 1, 2, 2, 3]
    while time.monotonic() < deadline and best_n < moore:
        k = rng.choice(ks)
        lo = max(2, best_n // (2 * k) + 1)
        G = rng.randint(lo, lo + max(2, lo // 10))
        divs = [a for a in range(1, G + 1) if G % a == 0]
        a = rng.choice(divs)
        b = G // a
        G, table = _translation_table(a, b)
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            break
        budget = min(remaining, 4.0)
        darts = _anneal(d, D, k, G, table, rng, time.monotonic() + budget)
        if darts is not None:
            n, e = _edges(k, G, darts, table)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
