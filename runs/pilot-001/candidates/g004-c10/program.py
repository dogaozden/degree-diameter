import itertools
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _reach_masks(n, adj, D):
    """Bitmask of vertices within distance D for every vertex (bit w set = w reachable)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return reach


def _repair_by_deletion(n, edges, D, deadline):
    """NEW: repair a near-valid bipartite graph by greedy vertex deletion.

    Repeatedly delete the vertex that lies in the most bad pairs (pairs at distance
    > D) until no bad pair remains. Deleting vertices keeps bipartiteness and never
    raises a degree, so a success is always a legal candidate (the caller re-checks
    it with lib.is_valid). Returns (n, edges) with zero bad pairs, or None.
    """
    cur_n, cur_e = n, list(edges)
    while cur_n > 0:
        if time.monotonic() >= deadline:
            return None
        adj = lib.adjacency(cur_n, cur_e)
        reach = _reach_masks(cur_n, adj, D)
        bad = [cur_n - r.bit_count() for r in reach]
        if sum(bad) == 0:
            return cur_n, cur_e
        v = max(range(cur_n), key=lambda x: bad[x])
        cur_e = [(a, b) for a, b in cur_e if a != v and b != v]
        if not cur_e:
            return None
        cur_n, cur_e = lib.relabel(cur_e)
    return None


def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D.

    Cost = number of vertex pairs at distance > D. Returns S with cost 0, or None.
    """
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:  # accept sideways moves to escape plateaus
            S, c = T, ct
    return S if c == 0 else None


def _search_lift(d, D, k, m, rng, iters, deadline):
    """Hill-climb Z_m voltages on a random d-regular bipartite base with k+k vertices.

    Returns (n, edges, cost) of the final lift; cost == 0 means it is valid.
    """
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.voltage_lift(2 * k, [tuple(x) for x in darts], m)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0:
            break
        if time.monotonic() > deadline:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        if m > 1:
            darts[j][2] = (old + rng.randrange(1, m)) % m
        n2, e2, c2 = evaluate()
        if c2 <= c:  # accept plateau moves too
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    return n, e, c


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # D = 3: projective plane with largest prime power q <= d - 1.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # D >= 4: generalized quadrangle W(q) with q + 1 <= d (diameter 4 <= D).
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Mixed search: Haar graphs with growing modulus, and random-base voltage lifts
    # whose near-misses are repaired by vertex deletion.
    haar_m, haar_miss = d + 1, 0
    while time.monotonic() < deadline:
        if rng.random() < 0.5 and haar_miss < 4:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
        else:
            k = rng.choice([1, 2, 3, 4])
            m = max(2, best_n // (2 * k) + 1)
            n_l, e_l, c_l = _search_lift(d, D, k, m, rng, 200, deadline)
            if c_l == 0:
                consider(n_l, e_l)
            elif c_l <= 40:
                # Near-valid lift: try to repair it by deleting bad vertices.
                rep_deadline = min(deadline, time.monotonic() + 0.08 * time_limit)
                r = _repair_by_deletion(n_l, e_l, D, rep_deadline)
                if r is not None:
                    consider(r[0], r[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
