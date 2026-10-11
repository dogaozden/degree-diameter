import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: projective plane incidence and generalized quadrangle W(q).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of W(q), a generalized quadrangle; diameter 4.

    Points are 0..P-1, lines are P..2P-1. Degree of every vertex is q + 1.
    """
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bold family: cyclic voltage lifts of the generalized quadrangle incidence
# graph W(q). The base is (q+1)-regular with diameter 4, so every lift keeps
# degree q+1 and the base is already valid for D = 5 at its own order.
# Lifts multiply the order by m. Voltages are annealed to kill all bad pairs,
# and near misses are repaired by deleting far-off vertices.
# ----------------------------------------------------------------------------

def _gq_darts(q):
    """Return (P, darts) where darts are (point, line) pairs of W(q) with line index in 0..P-1."""
    n, edges = _gq_w(q)
    P = n // 2
    darts = [(u, v - P) for u, v in edges]
    return P, darts


def _lift_adj(P, darts, m, volt):
    """Adjacency lists of the Z_m lift: point p fibre g joins line L fibre (g + volt) mod m."""
    N = 2 * P * m
    adj = [[] for _ in range(N)]
    for (p, L), a in zip(darts, volt):
        for g in range(m):
            x = p * m + g
            y = (P + L) * m + (g + a) % m
            adj[x].append(y)
            adj[y].append(x)
    return N, adj


def _reach(N, adj, D):
    """Bitmask per vertex of all vertices within distance D."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _bad_pairs(N, adj, D):
    """Ordered count of vertex pairs at distance more than D."""
    reach = _reach(N, adj, D)
    return sum(N - r.bit_count() for r in reach)


def _adj_to_edges(N, adj):
    return [(v, u) for v in range(N) for u in adj[v] if v < u]


def _search_lift(P, darts, m, D, rng, deadline, iters):
    """Simulated annealing over Z_m voltages. Returns (cost, N, adj) for the final state."""
    E = len(darts)
    volt = [rng.randrange(m) for _ in range(E)]
    N, adj = _lift_adj(P, darts, m, volt)
    cost = _bad_pairs(N, adj, D)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        e = rng.randrange(E)
        old = volt[e]
        new = rng.randrange(m - 1)
        if new >= old:
            new += 1
        volt[e] = new
        N, adj = _lift_adj(P, darts, m, volt)
        c2 = _bad_pairs(N, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            volt[e] = old
        T = max(0.3, T * 0.998)
    N, adj = _lift_adj(P, darts, m, volt)
    return cost, N, adj


def _delete(N, adj, dead):
    """Remove the dead vertices and relabel the survivors to 0..m-1."""
    new = {}
    for v in range(N):
        if v not in dead:
            new[v] = len(new)
    nadj = [[new[u] for u in adj[v] if u not in dead]
            for v in range(N) if v not in dead]
    return len(new), nadj


def _repair(N, adj, D, deadline, rng):
    """Delete far-off vertices in batches until diameter <= D. Returns (N, adj) or None."""
    while time.monotonic() < deadline:
        if N == 0:
            return None
        reach = _reach(N, adj, D)
        bad = [N - r.bit_count() for r in reach]
        if not any(bad):
            return N, adj
        bad_v = [v for v in range(N) if bad[v] > 0]
        rng.shuffle(bad_v)
        bad_v.sort(key=lambda v: -bad[v])
        batch = max(1, len(bad_v) // 12)
        dead = set(bad_v[:batch])
        N, adj = _delete(N, adj, dead)
    return None


def _gq_lift_search(d, D, rng, deadline, consider):
    """Anneal Z_2 and Z_3 lifts of W(q) for the largest prime power q <= min(d-1, 7)."""
    qs = [x for x in range(2, min(d - 1, 7) + 1) if lib.is_prime_power(x)]
    if not qs:
        return
    q = qs[-1]
    P, darts = _gq_darts(q)
    attempt = 0
    while time.monotonic() < deadline - 0.5:
        m = 3 if attempt % 4 == 3 else 2
        attempt += 1
        cost, N, adj = _search_lift(P, darts, m, D, rng, deadline, 2500)
        if cost == 0:
            consider(N, _adj_to_edges(N, adj))
            continue
        rd = min(deadline, time.monotonic() + 5.0)
        out = _repair(N, adj, D, rd, rng)
        if out is not None:
            n2, adj2 = out
            consider(n2, _adj_to_edges(n2, adj2))


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D >= 5:
        _gq_lift_search(d, D, rng, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
