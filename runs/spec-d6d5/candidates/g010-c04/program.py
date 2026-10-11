import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families for D = 3 and small cases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New construction: complete-bipartite voltage lifts (K_{d,d} base, all d^2
# darts used, one voltage per dart). Every vertex then has degree exactly d,
# the order is 2*d*G for a group of order G, and no degree is wasted on
# random permutations. Left translations are automorphisms of the lift, so
# BFS from the 2d identity-vertices (one per side and layer) decides the
# diameter exactly.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (d+j)*G + h.
# Dart (i, j) with voltage s joins A_i,g to B_j, mul(g, s) for every g.
# ----------------------------------------------------------------------------

def _groups_of_order(G, rng):
    """Multiplication tables of cyclic and semidirect groups Z_m x| Z_k2 of order G."""
    out = [lib.cyclic_group(G)[1]]
    for k2 in range(2, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:3]:
            out.append(lib.semidirect_group(m, k2, r)[1])
    return out


def _kdd_cost(d, D, G, T, volt, limit):
    """Pairs (representative, vertex) not reached within D. Early exit once above limit."""
    N = 2 * d * G
    adj = [[] for _ in range(N)]
    for i in range(d):
        row = volt[i]
        for g in range(G):
            a = i * G + g
            for j in range(d):
                b = (d + j) * G + T[row[j]][g]
                adj[a].append(b)
                adj[b].append(a)
    reps = [i * G for i in range(d)] + [(d + j) * G for j in range(d)]
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
        if total > limit:
            return total
    return total


def _kdd_anneal(d, D, G, T, rng, deadline, iters):
    """Simulated annealing over the d*d voltages. Returns (volt, cost)."""
    volt = [[rng.randrange(G) for _ in range(d)] for _ in range(d)]
    cost = _kdd_cost(d, D, G, T, volt, float("inf"))
    temp = 2.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, temp * 0.995)
        i = rng.randrange(d)
        j = rng.randrange(d)
        old = volt[i][j]
        new = rng.randrange(G)
        if new == old:
            continue
        limit = cost - temp * math.log(1.0 - rng.random())
        volt[i][j] = new
        c2 = _kdd_cost(d, D, G, T, volt, limit)
        if c2 <= limit:
            cost = c2
        else:
            volt[i][j] = old
    return volt, cost


def _kdd_edges(d, G, T, volt):
    """Edge list of the K_{d,d} voltage lift."""
    E = []
    for i in range(d):
        for g in range(G):
            for j in range(d):
                E.append((i * G + g, (d + j) * G + T[volt[i][j]][g]))
    return 2 * d * G, E


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Already at the Moore bound: nothing to gain (e.g. calibration case).
    if best_n >= lib._moore_bound(d, D):
        return best

    # Complete-bipartite voltage-lift search with growing group order.
    if d >= 2 and D >= 2:
        g_ok = best_n // (2 * d)
        while time.monotonic() < deadline:
            G = g_ok + 1 + rng.randrange(max(2, g_ok // 10))
            groups = _groups_of_order(G, rng)
            rng.shuffle(groups)
            for mul in groups[:3]:
                if time.monotonic() >= deadline:
                    break
                T = [[mul(g, s) for g in range(G)] for s in range(G)]
                volt, c = _kdd_anneal(d, D, G, T, rng, deadline, 800)
                if c == 0:
                    n, e = _kdd_edges(d, G, T, volt)
                    consider(n, e)
                    g_ok = max(g_ok, G)
                    break
            if best_n >= lib._moore_bound(d, D):
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
