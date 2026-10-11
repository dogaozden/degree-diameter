import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base families.
#   * PG(2, q) incidence graph (D = 3), Araujo-Pardo-Lopez graph (D = 3).
#   * W(q) generalized quadrangle incidence graph, degree q + 1, diameter 4.
# New in this version: for D >= 5 and d - 1 a prime power, the W(q) incidence
# graph is used as a base for Z_m voltage lifts (m = 2, 3). A lift keeps
# degree d and bipartiteness, and the search minimizes the number of pairs
# farther than D apart, using bitmask balls.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 23), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


# ----------------------------------------------------------------------------
# Voltage-lift search over Z_m with bitmask distance cost.
# ----------------------------------------------------------------------------

def _bad(N, adj, D):
    """Number of ordered vertex pairs at distance more than D (zero means diameter <= D)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _lift_cost(base_n, base_edges, volt, m, D):
    """Bad-pair count of the Z_m lift with the given voltages on the base edges."""
    N = base_n * m
    adj = [[] for _ in range(N)]
    for (u, v), a in zip(base_edges, volt):
        um = u * m
        vm = v * m
        for g in range(m):
            x = um + g
            y = vm + (g + a) % m
            adj[x].append(y)
            adj[y].append(x)
    return _bad(N, adj, D)


def _lift_search(base_n, base_edges, D, m, rng, deadline):
    """Simulated annealing over voltages. Returns (n, edges) of a lift with diameter <= D, or None."""
    E = len(base_edges)
    if E == 0:
        return None
    volt = [rng.randrange(m) for _ in range(E)]
    cost = _lift_cost(base_n, base_edges, volt, m, D)
    T = 1.5
    while cost > 0 and time.monotonic() < deadline:
        i = rng.randrange(E)
        old = volt[i]
        new = rng.randrange(m)
        if new == old:
            continue
        volt[i] = new
        c2 = _lift_cost(base_n, base_edges, volt, m, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            volt[i] = old
        T = max(0.2, T * 0.998)
    if cost != 0:
        return None
    darts = [(u, v, a) for (u, v), a in zip(base_edges, volt)]
    return lib.voltage_lift(base_n, darts, m)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(res):
        nonlocal best_n, best_e
        if res is None:
            return
        n, e = res
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    gq = None
    if D >= 3:
        consider(_best_pg(d))
        consider(_araujo(d))
    if D >= 4 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 9:
        gq = _gq_w(d - 1)
        consider(gq)

    # New family: Z_m voltage lifts of the generalized quadrangle incidence graph.
    if D >= 5 and gq is not None:
        base_n, base_e = gq
        now = time.monotonic()
        budget = max(0.0, end - now)
        for m, dl in ((2, now + 0.25 * budget), (3, end)):
            if time.monotonic() >= dl:
                continue
            consider(_lift_search(base_n, base_e, D, m, rng, dl))

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
