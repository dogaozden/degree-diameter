import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group voltage lifts over semidirect products with a fast two-stage evaluator.
# Dart (i, j, s) joins A_i,g to B_j,g*s for all g. Diameter <= D iff a BFS of
# depth D from each of the 2k base representatives reaches everything.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _search(d, D, k, G, rng, iters, deadline):
    """Hill-climb over voltages in a group of order G; returns (n, edges) or None."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    G = order
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = []
    for p in layers:
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_perm = perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = _right_perm(mul, G, new_s)
        c2 = _cost(k, G, D, darts, perms)
        if c2 <= cost or rng.random() < 0.02:
            cost = c2
        else:
            darts[idx][2] = old_s
            perms[idx] = old_perm

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# New construction: random bipartite union-of-matchings, then greedy vertex
# deletion repair. Start with a bipartite graph (A side 0..m-1, B side m..2m-1)
# built from d random perfect matchings, so every degree is <= d. Compute, for
# every vertex, how many other vertices it cannot reach within D steps, and
# delete the most-offending vertices in batches until no pair is bad. Deletion
# only lowers degrees and keeps the graph bipartite, so the output is valid by
# construction (and is re-checked by lib.is_valid in consider()).
# ----------------------------------------------------------------------------

def _reach_masks(adj, alive, vs, D):
    """Bitmask per vertex of all alive vertices within distance D (synchronous BFS rounds)."""
    N = len(alive)
    reach = [0] * N
    for v in vs:
        reach[v] = 1 << v
    for _ in range(D):
        new = reach[:]
        changed = False
        for v in vs:
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            if r != reach[v]:
                new[v] = r
                changed = True
        reach = new
        if not changed:
            break
    return reach


def _repair(d, D, m, rng, deadline):
    """Random d-matching-union bipartite graph with parts of size m, repaired by vertex deletion.

    Returns (n, edges) with diameter <= D, or None if the deadline passes or the graph empties.
    """
    N = 2 * m
    adj = [set() for _ in range(N)]
    for _ in range(d):
        p = list(range(m))
        rng.shuffle(p)
        for i in range(m):
            a, b = i, m + p[i]
            adj[a].add(b)
            adj[b].add(a)
    alive = [True] * N
    vs = list(range(N))
    while True:
        if time.monotonic() > deadline:
            return None
        n_alive = len(vs)
        if n_alive < 2:
            return None
        reach = _reach_masks(adj, alive, vs, D)
        bad = {v: n_alive - reach[v].bit_count() for v in vs}
        if sum(bad.values()) == 0:
            break
        k = max(1, n_alive // 60)
        order = sorted(vs, key=lambda v: (-bad[v], rng.random()))
        drop = [v for v in order[:k] if bad[v] > 0]
        for v in drop:
            alive[v] = False
            for u in adj[v]:
                adj[u].discard(v)
            adj[v] = set()
        vs = [v for v in vs if alive[v]]
    edges = [(v, u) for v in vs for u in adj[v] if v < u]
    if not edges:
        return None
    return lib.relabel(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
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

    if D >= 4 and time.monotonic() < start + 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing to gain, return instantly.
    if best_n >= lib._moore_bound(d, D):
        return best

    # Phase 1: group voltage-lift search.
    group_deadline = start + 0.45 * time_limit
    while time.monotonic() < group_deadline:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
        res = _search(d, D, k, G, rng, 600, group_deadline)
        if res is not None:
            consider(res[0], res[1])

    # Phase 2: random matching-union start, repaired by greedy deletion.
    repair_deadline = start + 0.75 * time_limit
    while time.monotonic() < repair_deadline:
        N = int(best_n * rng.uniform(1.2, 1.7))
        m = max(2, N // 2)
        res = _repair(d, D, m, rng, repair_deadline)
        if res is not None and res[0] > best_n:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
