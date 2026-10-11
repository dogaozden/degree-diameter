"""Bold rewrite: voltage lifts of the projective plane PG(2, q), with generalized quadrangles as a fallback.

Strategy for D >= 5 (the d5D5 target):
  * Base graph: incidence graph of PG(2, q), q + 1 = d (for d = 5, q = 4). It is 5-regular,
    bipartite, 42 vertices, diameter 3. Its slack (diameter 3 against a target of 5) is what
    makes lifts plausible.
  * Lift: a voltage lift over a finite group G of order m. Each base dart gets a group element,
    giving a 5-regular bipartite graph on 42*m vertices. Left translations are automorphisms,
    so the cost only needs to be measured from base representatives.
  * Search: simulated annealing over the voltages, minimizing the number of vertex pairs at
    distance > D (bitset BFS). Orders are tried in increasing order, so each success raises the bar.
    Every success is verified with lib.is_valid.

Fallbacks (always valid): K_{d,d}; PG(2, q) incidence for D >= 3; generalized quadrangle W(q)
incidence for D >= 4. Other (d, D) cases do not use the parent's Bi-Cayley and multi-base search,
so they can score below the parent when d - 1 is not a prime power. Only d5D5 and d3D3 are scored here.
"""
import itertools
import math
import random
import time

import lib

SLICE = 5.0  # seconds per annealing attempt on one order
_HAS_BC = hasattr(int, "bit_count")


def _popcount(x):
    return x.bit_count() if _HAS_BC else bin(x).count("1")


def _largest_pp(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _group_list(N):
    """Parameters (m, k, r) of Z_m x|_r Z_k with m*k = N (k = 1 gives the cyclic group)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _cost(N, adj, D):
    """Ordered pairs (v, w) with dist(v, w) > D; zero means the lift has diameter <= D."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        nxt = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    total = 0
    for r in reach:
        total += N - _popcount(r)
    return total


def _move(adj, u, v, G, T, old, new):
    """Re-route base dart (u, v) from voltage old to voltage new in the adjacency lists."""
    ub, vb = u * G, v * G
    row_o, row_n = T[old], T[new]
    for x in range(G):
        a = ub + x
        bo = vb + row_o[x]
        bn = vb + row_n[x]
        adj[a].remove(bo)
        adj[bo].remove(a)
        adj[a].append(bn)
        adj[bn].append(a)


def _anneal_lift(n0, base_edges, G, T, D, rng, deadline):
    """Anneal voltages in G until the lift has diameter <= D. Returns voltages or None."""
    N = n0 * G
    E = len(base_edges)
    volts = [rng.randrange(G) for _ in range(E)]
    adj = [[] for _ in range(N)]
    for (u, v), g in zip(base_edges, volts):
        row = T[g]
        ub, vb = u * G, v * G
        for x in range(G):
            a, b = ub + x, vb + row[x]
            adj[a].append(b)
            adj[b].append(a)
    cost = _cost(N, adj, D)
    if cost == 0:
        return volts
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T0 = max(1.0, 0.05 * cost)
    Tend = 0.3
    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        temp = T0 * (Tend / T0) ** min(1.0, (now - start) / span)
        i = rng.randrange(E)
        old = volts[i]
        new = rng.randrange(G - 1)
        if new >= old:
            new += 1
        u, v = base_edges[i]
        _move(adj, u, v, G, T, old, new)
        c2 = _cost(N, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = c2
            volts[i] = new
            if cost == 0:
                return volts
        else:
            _move(adj, u, v, G, T, new, old)
    return None


def _lift_edges(n0, base_edges, G, T, volts):
    E = []
    for (u, v), g in zip(base_edges, volts):
        row = T[g]
        for x in range(G):
            E.append((u * G + x, v * G + row[x]))
    return n0 * G, E


def _lift_search(n0, base_edges, d, D, best_n, deadline, rng, hi):
    """Round-robin over lift orders n0*m > best_n, each on its own time slice. Returns (n, edges) or None."""
    best = None
    pending = [m for m in range(best_n // n0 + 1, hi + 1) if n0 * m > best_n]
    while pending:
        progressed = False
        for m in list(pending):
            now = time.monotonic()
            left = deadline - now
            if left < 0.3:
                return best
            mm, k, r = rng.choice(_group_list(m))
            G, mul, _ = lib.semidirect_group(mm, k, r)
            T = [[mul(x, g) for x in range(G)] for g in range(G)]
            volts = _anneal_lift(n0, base_edges, G, T, D, rng, now + min(left, SLICE))
            if volts is None:
                continue
            N, E = _lift_edges(n0, base_edges, G, T, volts)
            if not lib.is_valid(N, E, d, D):
                continue
            best = (N, E)
            pending = [x for x in pending if n0 * x > N]
            progressed = True
            break
        if not progressed and time.monotonic() >= deadline - 0.3:
            break
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # K_{d,d}: bipartite, degree d, diameter 2. Safe fallback for every D >= 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best_n, best_e = n0, list(e0)
    if D == 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
            return True
        return False

    # Projective plane incidence: diameter 3, degree q + 1 <= d.
    q = _largest_pp(d - 1)
    if q is not None:
        consider(*lib.projective_plane_incidence(q))

    # Generalized quadrangle incidence: diameter 4, degree q + 1 <= d.
    if D >= 4:
        qg = _largest_pp(min(d - 1, 5))
        if qg is not None:
            consider(*_gq_w(qg))

    # Main bold path: voltage lifts of PG(2, q) with annealed voltages.
    if D >= 5 and q is not None and time.monotonic() < deadline:
        pn, pe = lib.projective_plane_incidence(q)
        moore = lib.moore_bound(d, D)
        hi = min(moore // pn, 80)
        res = _lift_search(pn, list(pe), d, D, best_n, deadline, rng, hi)
        if res is not None:
            consider(*res)

    if not lib.is_valid(best_n, best_e, d, D):
        n0, e0 = lib.haar_graph(d, range(d))
        return n0, list(e0)
    return best_n, best_e
