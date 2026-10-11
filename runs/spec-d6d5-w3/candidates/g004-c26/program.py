import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Baseline constructions (diameter 3 records and a valid fallback).
# ----------------------------------------------------------------------------

def _pg_incidence(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2, q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Fast bad-pair counter on adjacency lists (bitmask ball growth).
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    prev = [1 << v for v in range(n)]
    for _ in range(D):
        cur = []
        for v in range(n):
            x = prev[v]
            for u in adj[v]:
                x |= prev[u]
            cur.append(x)
        prev = cur
    return sum(n - b.bit_count() for b in prev) // 2


# ----------------------------------------------------------------------------
# NEW ROUTINE: degree-preserving 2-switch annealing.
#
# Given a bipartite graph in which every edge is oriented (A-side, B-side),
# a switch replaces (a,b),(c,e) by (a,e),(c,b). Degrees and bipartiteness are
# preserved exactly, so a near-miss regular lift can be repaired at fixed order
# instead of being shrunk by vertex deletion. The objective is the exact number
# of bad pairs at distance > D.
# ----------------------------------------------------------------------------

def _swap_anneal(n, edges, D, deadline, rng):
    E = [[u, v] for u, v in edges]
    m = len(E)
    if m < 2:
        return None
    keys = set((min(a, b), max(a, b)) for a, b in E)
    cost = _bad_pairs(n, _adjacency(n, E), D)
    T = 1.5
    while cost > 0 and time.monotonic() < deadline:
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, f = E[j]
        if a == c or b == f:
            continue
        k1 = (min(a, f), max(a, f))
        k2 = (min(c, b), max(c, b))
        if k1 in keys or k2 in keys:
            continue
        E[i] = [a, f]
        E[j] = [c, b]
        c2 = _bad_pairs(n, _adjacency(n, E), D)
        T = max(0.1, T * 0.9995)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            keys.discard((min(a, b), max(a, b)))
            keys.discard((min(c, f), max(c, f)))
            keys.add(k1)
            keys.add(k2)
            cost = c2
        else:
            E[i] = [a, b]
            E[j] = [c, f]
    if cost == 0:
        return [(u, v) for u, v in E]
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2.
# Vertices: A_i,g = i*G + g, B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,g*s for all g.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(60):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 8, 10, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in range(1, m)
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        order, mul, _ = lib.semidirect_group(m, k2, r)
        return order, mul
    return None


def _lift_cost(k, G, D, darts, perms):
    """Pairs (orbit representative, vertex) not reached within D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for src in [i * G for i in range(k)] + [(k + j) * G for j in range(k)]:
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
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _lift_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _lift_anneal(d, D, k, G, mul, rng, deadline, iters):
    """Anneal voltages so the lift has diameter <= D. Returns (darts, perms, cost)."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_p = perms[idx]
        s = rng.randrange(G)
        darts[idx][2] = s
        perms[idx] = [mul(g, s) for g in range(G)]
        c2 = _lift_cost(k, G, D, darts, perms)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            darts[idx][2] = old_s
            perms[idx] = old_p
        T = max(0.05, T * 0.995)
    return darts, perms, cost


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    target = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, list(e))
            best_n = n

    if D >= 3:
        pg = _pg_incidence(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Calibration shortcut: a graph at the Moore bound cannot be beaten.
    if best_n >= target:
        return best

    ks = [1, 1, 2, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        lo = best_n // (2 * k) + 1
        hi = lo + max(2, lo // 40)
        G = rng.randint(lo, hi)
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g

        darts, perms, c = _lift_anneal(d, D, k, order, mul, rng, deadline, 800)
        if c == 0:
            n, e = _lift_edges(k, order, darts, perms)
            consider(n, e)
            continue

        # Near miss: repair the fixed-order lift with degree-preserving swaps.
        n, e = _lift_edges(k, order, darts, perms)
        if time.monotonic() >= deadline:
            break
        bp = _bad_pairs(n, _adjacency(n, e), D)
        if bp <= 3 * n:
            swap_deadline = min(deadline, time.monotonic() + 10.0)
            fixed = _swap_anneal(n, e, D, swap_deadline, rng)
            if fixed is not None:
                consider(n, fixed)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
