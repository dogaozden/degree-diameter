import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_kg, searched by annealing.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h, with G = m*kg.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for every g in the group.
# Each of the d layers is a permutation of the k base vertices, so every
# vertex has degree d. The left action of the group is an automorphism, so
# distances from the 2k representatives A_{i,e} and B_{j,e} determine the
# diameter.
#
# Fallbacks: K_{d,d} (diameter 2), the projective-plane incidence graph when
# d-1 is a prime power, and the Araujo-Pardo-Lopez graph when d-2 is a prime
# power. Every candidate is checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------


def _sd_table(m, kg, r):
    """Multiplication table T[x, y] of Z_m x| Z_kg, with (a,b)(c,d) = (a + r^b c, b + d)."""
    G = m * kg
    pw = np.array([pow(r, b, m) for b in range(kg)], dtype=np.int64)
    x = np.arange(G, dtype=np.int64)
    a = x // kg
    b = x % kg
    first = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    second = (b[:, None] + b[None, :]) % kg
    return first * kg + second


def _group_options(G):
    """Return (m, kg, r) triples giving a group of order G (kg <= 64, m >= 2)."""
    opts = []
    for kg in range(1, min(G, 64) + 1):
        if G % kg:
            continue
        m = G // kg
        if m < 2:
            continue
        if kg == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, kg, m) == 1 % m:
                opts.append((m, kg, r))
    return opts


def _build_adj(G, k, darts, tabs):
    """Adjacency lists of the lift described by darts (duplicates are harmless for BFS)."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        pm = tabs[s]
        bi = i * G
        bj = (k + j) * G
        for g in range(G):
            a = bi + g
            b = bj + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _bad(N, adj, reps, D):
    """Total number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
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


def _edges(k, G, darts, tabs):
    """Full edge list of the lift; A vertices precede B vertices, so each edge is stored as (A, B)."""
    E = set()
    for i, j, s in darts:
        pm = tabs[s]
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, tabs, rng, deadline, iters):
    """Anneal voltages and layer permutations. Returns (ok, darts, cost)."""
    N = 2 * k * G
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])

    def score():
        return _bad(N, _build_adj(G, k, darts, tabs), reps, D)

    cost = score()
    T = 1.5
    for _ in range(iters):
        if cost == 0 or time.monotonic() >= deadline:
            break
        T = max(0.2, T * 0.998)
        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            darts[idx][2] = rng.randrange(G)
            new = score()
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            new = score()
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return cost == 0, darts, cost


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    base_n, base_e = lib.haar_graph(d, range(d))
    if D == 2:
        return base_n, base_e

    best_n, best_e = base_n, base_e
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Algebraic baselines (diameter 3).
    if lib.is_prime_power(d - 1):
        pn, pe = lib.projective_plane_incidence(d - 1)
        consider(pn, pe)
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            an, ae = lib.araujo_lopez_graph(d - 2)
            consider(an, ae)
        except Exception:
            pass

    # Main search: bi-Cayley lifts aimed just above the current best order.
    ks = [1, 1, 1, 2, 2, 3, 4]
    while time.monotonic() < deadline and best_n < moore:
        k = rng.choice(ks)
        need = best_n + 2
        lo = -(-need // (2 * k))  # ceil(need / (2k))
        G = lo
        if rng.random() < 0.5:
            G += rng.randint(0, max(1, lo // 8))
        opts = _group_options(G)
        if not opts:
            continue
        m, kg, r = rng.choice(opts)
        T = _sd_table(m, kg, r)
        tabs = T.T.tolist()  # tabs[s][g] = g * s
        att_deadline = min(deadline, time.monotonic() + 8.0)
        ok, darts, _cost = _anneal(d, D, k, G, tabs, rng, att_deadline, 3000)
        if ok:
            n, e = _edges(k, G, darts, tabs)
            consider(n, e)

    if not lib.is_valid(best_n, best_e, d, D):
        return base_n, base_e
    return best_n, best_e
