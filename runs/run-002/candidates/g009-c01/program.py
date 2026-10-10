import itertools
import math
import random
import time

import lib


_BIG = 10 ** 9


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


# ----------------------------------------------------------------------------
# Algebraic starting points (unchanged from the parent).
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
# New search: simulated annealing over bi-Cayley lifts.
#
# Base: k A-vertices, k B-vertices. Layer l (l = 0..d-1) is a permutation tj[l]
# of the B-indices, with a voltage sv[l][i] in a group H of order G. Dart
# (l, i) joins A_{i,g} to B_{tj[l][i], g * sv[l][i]} for all g in H.
#
# Left multiplication is an automorphism, so the diameter is <= D iff a BFS of
# depth D from each of the 2k base representatives reaches every vertex.
#
# Moves: change one voltage, or swap the B-targets of two darts in one layer.
# Both keep every vertex at degree exactly d. Acceptance follows an annealing
# schedule on the number of unreached (representative, vertex) pairs.
# ----------------------------------------------------------------------------

def _random_group(G, rng):
    """Return (order, mul) for a random group of order G: cyclic or semidirect Z_m x| Z_k2."""
    divs = [t for t in range(1, G + 1) if G % t == 0 and G // t >= 2]
    for _ in range(60):
        k2 = 1 if (not divs or rng.random() < 0.4) else rng.choice(divs)
        m = G // k2
        if k2 == 1:
            r = 1
        else:
            cands = [x for x in rng.sample(range(1, m), min(m - 1, 80))
                     if math.gcd(x, m) == 1 and pow(x, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    order, mul, _ = lib.semidirect_group(G, 1, 1)
    return order, mul


def _right_perm(mul, G, s):
    """Permutation g -> g * s of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(d, k, G, D, tj, sv, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    keys = set()
    for l in range(d):
        for i in range(k):
            key = (i, tj[l][i], sv[l][i])
            if key in keys:
                return _BIG  # duplicate dart would create a duplicate edge
            keys.add(key)
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for l in range(d):
        for i in range(k):
            ba = i * G
            bb = (k + tj[l][i]) * G
            pm = perms[l][i]
            for g in range(G):
                a = ba + g
                b = bb + pm[g]
                adj[a].append(b)
                adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
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


def _edges(d, k, G, tj, perms):
    E = set()
    for l in range(d):
        for i in range(k):
            bb = (k + tj[l][i]) * G
            pm = perms[l][i]
            for g in range(G):
                E.add((i * G + g, bb + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, rng, deadline):
    """Anneal over voltages and base targets for a group of order about G.

    Returns (n, edges) with diameter <= D, or None if the deadline passes first.
    """
    order, mul = _random_group(G, rng)
    G = order
    tj = [rng.sample(range(k), k) for _ in range(d)]
    sv = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    perms = [[_right_perm(mul, G, sv[l][i]) for i in range(k)] for l in range(d)]
    cost = _cost(d, k, G, D, tj, sv, perms)

    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 1.0, 0.03

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)

        if rng.random() < 0.5 or k < 2:
            l = rng.randrange(d)
            i = rng.randrange(k)
            old_s = sv[l][i]
            old_pm = perms[l][i]
            new_s = rng.randrange(G)
            sv[l][i] = new_s
            perms[l][i] = _right_perm(mul, G, new_s)
            c2 = _cost(d, k, G, D, tj, sv, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                sv[l][i] = old_s
                perms[l][i] = old_pm
        else:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            tj[l][i1], tj[l][i2] = tj[l][i2], tj[l][i1]
            c2 = _cost(d, k, G, D, tj, sv, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                tj[l][i1], tj[l][i2] = tj[l][i2], tj[l][i1]

    if cost == 0:
        return _edges(d, k, G, tj, perms)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.6 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = _moore(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: annealed bi-Cayley lifts, targeting orders just above the current best.
    while time.monotonic() < deadline and best_n < moore:
        k = rng.choice([1, 1, 2, 2, 3, 4])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(2, base // 10 + 2)))
        now = time.monotonic()
        sub = min(deadline, now + max(1.5, 0.3 * (deadline - now)))
        res = _anneal(d, D, k, G, rng, sub)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
