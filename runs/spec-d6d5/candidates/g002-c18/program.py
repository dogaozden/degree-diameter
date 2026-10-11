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
# Group-voltage lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,g*s for every g in the group.
# Left multiplication is an automorphism, so the diameter is <= D iff every
# one of the 2k representatives (identity of each class) reaches all vertices
# within distance D.
#
# NEW HELPER: multi-source bitmask coverage cost.
# Instead of one BFS per representative, every vertex v carries an int R[v]
# whose bit t is set when representative t lies within distance (current
# round) of v. Each round ORs neighbour masks, so the whole check is
# O(D * N * d) operations on tiny ints. The cost is
#     2k * N - sum_v popcount(R_D[v]),
# which is zero exactly when the lift is valid. Early exit happens as soon as
# a round changes nothing.
# ----------------------------------------------------------------------------

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


def _adjacency(k, G, N, darts, perms):
    """Adjacency lists of the lift described by darts and their permutation tables."""
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ib = i * G
        bb = (k + j) * G
        for x in range(G):
            a = ib + x
            b = bb + pm[x]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _reach_cost(k, G, D, adj):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
    N = len(adj)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    R = [0] * N
    for t, v in enumerate(reps):
        R[v] |= 1 << t
    for _ in range(D):
        new = [0] * N
        changed = False
        for v in range(N):
            acc = R[v]
            for u in adj[v]:
                acc |= R[u]
            if acc != R[v]:
                changed = True
            new[v] = acc
        R = new
        if not changed:
            break
    covered = 0
    for v in range(N):
        covered += R[v].bit_count()
    return len(reps) * N - covered


def _search(d, D, k, G, rng, iters, deadline):
    """Simulated annealing over voltages in a semidirect group of order about G.

    Returns (n, edges) with diameter <= D, or None.
    """
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    G = order
    if k * G < d:
        return None
    N = 2 * k * G

    keys = set()
    darts = []
    for _layer in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            j = p[i]
            s = rng.randrange(G)
            tries = 0
            while (i, j, s) in keys and tries < 50:
                s = rng.randrange(G)
                tries += 1
            if (i, j, s) in keys:
                return None
            keys.add((i, j, s))
            darts.append([i, j, s])

    perms = [[mul(x, s) for x in range(G)] for _, _, s in darts]
    cost = _reach_cost(k, G, D, _adjacency(k, G, N, darts, perms))
    best_cost = cost
    best_darts = [list(x) for x in darts]
    best_perms = list(perms)

    T0 = 2.0
    for t in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.05
        idx = rng.randrange(len(darts))
        i, j, old_s = darts[idx]
        new_s = rng.randrange(G)
        if new_s == old_s or (i, j, new_s) in keys:
            continue
        old_pm = perms[idx]
        perms[idx] = [mul(x, new_s) for x in range(G)]
        darts[idx][2] = new_s
        c2 = _reach_cost(k, G, D, _adjacency(k, G, N, darts, perms))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            keys.discard((i, j, old_s))
            keys.add((i, j, new_s))
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_darts = [list(x) for x in darts]
                best_perms = list(perms)
        else:
            darts[idx][2] = old_s
            perms[idx] = old_pm

    if best_cost != 0:
        return None
    E = set()
    for (i, j, _s), pm in zip(best_darts, best_perms):
        for x in range(G):
            E.add((i * G + x, (k + j) * G + pm[x]))
    return N, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    # Calibration cases that already meet the Moore bound need no search.
    if best_n >= lib._moore_bound(d, D):
        return best

    # Main search: annealed group voltage lifts with 1-2 base vertices per side.
    # Group orders are sampled just above the current best, since beating the
    # record needs order close to best_n / (2k).
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 2])
        base = best_n // (2 * k)
        spread = max(3, base // 10)
        G = max(2, base + 1 + rng.randrange(spread))
        try:
            res = _search(d, D, k, G, rng, 3000, deadline)
        except Exception:
            res = None
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
