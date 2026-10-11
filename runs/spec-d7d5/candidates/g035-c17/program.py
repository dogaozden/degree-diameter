import math
import random
import time

import numpy as np

import lib

# Idea (new in this version): a Haar graph H(Gamma, S) over a finite group Gamma
# (Gamma = Z_m x|_r Z_k2, order near the record) is bipartite and has degree |S|.
# Left multiplication is an automorphism, so the diameter is at most D exactly when
# the ball of radius D around A_e and around B_e covers every vertex. A greedy
# coverage builder chooses the connection set S one element at a time, maximizing
# the number of (vertex, root) pairs reached. Simulated annealing then polishes S.
# Group order is pushed upward from a Moore-based starting point, so each success
# raises the target order.

_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x|_r Z_k2; element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h.
    """
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _sample_group_of_order(G, rng):
    """Return (m, k2, r) with m*k2 == G, or None."""
    divs = [k for k in range(1, min(G, 40) + 1) if G % k == 0]
    k2 = rng.choice(divs)
    m = G // k2
    if k2 == 1:
        return m, 1, 1
    if k2 == 2 and m > 2 and rng.random() < 0.3:
        r = m - 1
        if math.gcd(r, m) == 1 and pow(r, 2, m) == 1 % m:
            return m, 2, r
    for _ in range(100):
        r = rng.randrange(2, m) if m > 2 else 1
        if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
            return m, k2, r
    return None


def _row(G, Ts, Invs, s):
    """Neighbour map of one layer with voltage s: A_g -> B_{g s}, B_h -> A_{h s^-1}."""
    row = np.empty(2 * G, dtype=np.int64)
    row[:G] = G + Ts[s]
    row[G:] = Invs[s]
    return row


def _reach(G, rows, D):
    """Bitmask per vertex: bit 0 = within D of A_e, bit 1 = within D of B_e."""
    reach = np.zeros(2 * G, dtype=np.int64)
    reach[0] = 1
    reach[G] = 2
    for _ in range(D):
        new = reach.copy()
        for row in rows:
            new |= reach[row]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(G, rows, D):
    """Number of (root, vertex) pairs not yet within distance D."""
    return 4 * G - int(_POP[_reach(G, rows, D)].sum())


def _greedy(G, Ts, Invs, d, D, rng, deadline, pool_size):
    """Greedily choose d distinct connection elements maximizing covered pairs."""
    chosen, rows = [], []
    for _ in range(d):
        if time.monotonic() > deadline:
            return None
        pool = [s for s in range(G) if s not in chosen]
        if len(pool) > pool_size:
            pool = rng.sample(pool, pool_size)
        best_sc, best_s, best_row = -1.0, None, None
        for s in pool:
            row = _row(G, Ts, Invs, s)
            sc = int(_POP[_reach(G, rows + [row], D)].sum()) + 0.5 * rng.random()
            if sc > best_sc:
                best_sc, best_s, best_row = sc, s, row
        chosen.append(best_s)
        rows.append(best_row)
    return chosen


def _anneal(G, Ts, Invs, d, D, S, rng, deadline, patience):
    """Annealing over the connection set; returns S if all pairs are covered, else None."""
    rows = [_row(G, Ts, Invs, s) for s in S]
    cost = _unreached(G, rows, D)
    inS = set(S)
    best, last, t = cost, 0, 0
    temp = 0.7
    while cost and time.monotonic() < deadline and t - last < patience:
        t += 1
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in inS:
            continue
        old = S[i]
        rows2 = list(rows)
        rows2[i] = _row(G, Ts, Invs, new)
        c2 = _unreached(G, rows2, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            S[i] = new
            rows = rows2
            inS.discard(old)
            inS.add(new)
            cost = c2
            if cost < best:
                best, last = cost, t
    return list(S) if cost == 0 else None


def _haar_edges(G, Ts, S):
    edges = []
    for s in S:
        col = G + Ts[s]
        edges.extend((g, int(col[g])) for g in range(G))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: diameter 2, always valid for D >= 2
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if d >= 2 and D >= 2:
        moore_half = lib._moore_bound(d, D) // 2
        G_target = max(best_n // 2 + 1, int(0.35 * moore_half))
        while time.monotonic() < deadline:
            G = G_target + rng.randrange(0, 4)
            g = _sample_group_of_order(G, rng)
            if g is None:
                continue
            m, k2, r = g
            Gg, Ts, Invs = _group_tables(m, k2, r)
            trial_deadline = min(deadline, time.monotonic() + 6.0)
            S = _greedy(Gg, Ts, Invs, d, D, rng, trial_deadline, pool_size=200)
            if S is None:
                continue
            S = _anneal(Gg, Ts, Invs, d, D, S, rng, trial_deadline, patience=20000)
            if S is not None:
                consider(2 * Gg, _haar_edges(Gg, Ts, S))
                G_target = max(G_target, Gg + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
