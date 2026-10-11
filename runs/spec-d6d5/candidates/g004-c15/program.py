import itertools
import math
import random
import time

import numpy as np

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
# Group-voltage lifts over semidirect products.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h, for base size k.
# Dart (i, j, s) joins A_i,g to B_j,g*s for every g in the group.
#
# Layer t is a perfect matching between the A and B vertices (each layer
# gives one dart per A_i, and the layer's j's form a permutation), so the lift
# is d-regular and its adjacency fits in an (N, d) array: nb[v, t] is the
# layer-t partner of v.
#
# Left multiplication by any h is an automorphism, so the diameter is <= D iff
# a BFS of depth D from each of the 2k representatives reaches every vertex.
# The BFS is vectorised with numpy, which is the main speed gain over plain
# Python adjacency lists and lets the annealer run many more moves per group.
#
# Search: simulated annealing over voltages, keeping the best state seen.
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


def _build_nb(k, G, d, darts, perms, N):
    """Return the (N, d) partner array: column t holds the layer-t perfect matching."""
    nb = np.empty((N, d), dtype=np.int64)
    ar = np.arange(G, dtype=np.int64)
    for idx, ((i, j, _s), pm) in enumerate(zip(darts, perms)):
        t = idx // k
        a = i * G + ar
        b = (k + j) * G + pm
        nb[a, t] = b
        nb[b, t] = a
    return nb


def _cost(k, G, D, nb, N):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            cand = nb[front].ravel()
            cand = cand[~seen[cand]]
            if cand.size == 0:
                break
            cand = np.unique(cand)
            seen[cand] = True
            front = cand
        total += N - int(seen.sum())
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + int(pm[g])))
    return 2 * k * G, sorted(E)


def _search(d, D, k, G, rng, iters, deadline):
    """Simulated annealing over voltages in a group of order G.

    Base: k A-vertices and k B-vertices; each layer is a perfect matching.
    Returns (n, edges) with diameter <= D, or None.
    """
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    G = order
    N = 2 * k * G

    cache = {}

    def perm(s):
        p = cache.get(s)
        if p is None:
            p = np.array([mul(x, s) for x in range(G)], dtype=np.int64)
            cache[s] = p
        return p

    def evaluate(dts, prms):
        if len({(i, j, s) for i, j, s in dts}) < len(dts):
            return _BIG  # duplicate darts would waste degree
        nb = _build_nb(k, G, d, dts, prms, N)
        return _cost(k, G, D, nb, N)

    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = []
    for p in layers:
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [perm(s) for _, _, s in darts]
    cost = evaluate(darts, perms)

    best_cost = cost
    best_darts = [list(x) for x in darts]
    best_perms = list(perms)

    T0 = 3.0
    for t in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.05
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_perm = perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = perm(new_s)
        c2 = evaluate(darts, perms)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_darts = [list(x) for x in darts]
                best_perms = list(perms)
        else:
            darts[idx][2] = old_s
            perms[idx] = old_perm

    if best_cost == 0:
        return _edges(k, G, best_darts, best_perms)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 3.0)
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: annealed group voltage lifts with 1-3 base vertices per side.
    # Target group orders just above the current best. The vectorised cost
    # makes each attempt cheap, so allow longer anneals per group.
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        res = _search(d, D, k, G, rng, 4000, deadline)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
