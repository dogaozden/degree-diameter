import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Algebraic baselines (used only when they beat the fallback).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q), q the largest prime power with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo/Lopez record family for D = 3 when d - 2 is a prime power."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Search family: bi-Cayley lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,g*s for every g in the group.
# Left multiplication is an automorphism, so each class is one orbit and the
# diameter condition reduces to BFS of depth D from 2k representatives.
#
# Each layer is a permutation of the k base indices, so every base vertex has
# degree exactly d. Search is simulated annealing over darts, with two moves:
# change a voltage, or swap the targets of two darts in the same layer.
# Cost is the number of (representative, vertex) pairs not reached within D.
# ----------------------------------------------------------------------------

def _make_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order exactly G, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = []
            for _ in range(60):
                r = rng.randrange(1, m)
                if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                    cands.append(r)
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        if order == G:
            return order, mul
    return None


def _cost(k, G, D, darts, R):
    """Unreached (representative, vertex) pairs within distance D. Zero means valid."""
    if len(set(darts)) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        ba = i * G
        bb = (k + j) * G
        Rs = R[s]
        for g in range(G):
            a = ba + g
            b = bb + Rs[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = list(range(0, k * G, G)) + list(range(k * G, N, G))
    total = 0
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
    return total


def _edges(k, G, darts, R):
    E = []
    for i, j, s in darts:
        Rs = R[s]
        for g in range(G):
            E.append((i * G + g, (k + j) * G + Rs[g]))
    return 2 * k * G, E


def _anneal(d, D, k, G, R, rng, iters, deadline):
    """Simulated annealing over darts. Returns (n, edges) with diameter <= D, or None."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append((i, p[i], rng.randrange(G)))
    cost = _cost(k, G, D, darts, R)
    best_c = cost
    best_darts = list(darts)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 2.0 * (0.05 / 2.0) ** (it / iters)
        cand = list(darts)
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            i, j, _ = cand[idx]
            cand[idx] = (i, j, rng.randrange(G))
        else:
            l = rng.randrange(d)
            a = l * k + rng.randrange(k)
            b = l * k + rng.randrange(k)
            if a == b:
                continue
            ia, ja, sa = cand[a]
            ib, jb, sb = cand[b]
            cand[a] = (ia, jb, sa)
            cand[b] = (ib, ja, sb)
        c2 = _cost(k, G, D, cand, R)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            darts = cand
            cost = c2
            if cost < best_c:
                best_c = cost
                best_darts = list(darts)

    if best_c == 0:
        return _edges(k, G, best_darts, R)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + min(0.8 * time_limit, time_limit - 8.0)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2 or d < 2:
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    rng = random.Random(seed)

    # Main search: aim for group orders that beat the current best.
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        lo = best_n // (2 * k) + 1
        G = lo + rng.randrange(0, 4)
        grp = _make_group(G, rng)
        if grp is None:
            continue
        order, mul = grp
        R = [[mul(g, s) for g in range(order)] for s in range(order)]
        res = _anneal(d, D, k, order, R, rng, 1200, deadline)
        if res is not None:
            consider(res[0], res[1])

    return best
