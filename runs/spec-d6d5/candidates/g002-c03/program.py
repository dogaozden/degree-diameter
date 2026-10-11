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
# Left multiplication is an automorphism, so diameter <= D iff a radius-D ball
# from each of the 2k representatives covers everything.
#
# NEW HELPER: orbit-reach cost in numpy. Instead of Python BFS over adjacency
# lists, reach sets are boolean (k, G) arrays per side and each radius step is
# a gather (take_along_axis) plus a scatter-add over all darts at once.
#
# NEW MOVE: besides re-voltaging a dart, swap the B-targets of two A-vertices
# inside one layer. Each layer is a permutation, so degrees stay exactly d.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul, inv) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
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
            order, mul, inv = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul, inv
    return None


def _orbit_cost_np(k, G, D, I, J, PERM, SINV):
    """Missing (representative, vertex) pairs at distance > D. Zero means valid.

    I, J: dart endpoints (A index, B index). PERM[e, g] = g*s_e. SINV[e, b] = b*s_e^{-1}.
    """
    total = 0
    N = 2 * k * G
    for side in (0, 1):
        for x in range(k):
            RA = np.zeros((k, G), dtype=bool)
            RB = np.zeros((k, G), dtype=bool)
            if side == 0:
                RA[x, 0] = True
            else:
                RB[x, 0] = True
            for _ in range(D):
                gb = np.take_along_axis(RB[J], PERM, axis=1)   # A-side neighbours
                nA = np.zeros((k, G), dtype=np.int32)
                np.add.at(nA, I, gb.astype(np.int32))
                ga = np.take_along_axis(RA[I], SINV, axis=1)   # B-side neighbours
                nB = np.zeros((k, G), dtype=np.int32)
                np.add.at(nB, J, ga.astype(np.int32))
                newRA = RA | (nA > 0)
                newRB = RB | (nB > 0)
                if np.array_equal(newRA, RA) and np.array_equal(newRB, RB):
                    break
                RA, RB = newRA, newRB
            total += N - int(RA.sum()) - int(RB.sum())
    return total


def _search(d, D, k, G0, rng, iters, deadline):
    """Simulated annealing over voltages and B-target swaps in a group of order about G0.

    Returns (n, edges) with diameter <= D, or None.
    """
    g = _sample_group(G0, rng)
    if g is None:
        return None
    G, mul, inv = g

    darts = []
    for _layer in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])

    cache = {}

    def perm_of(s):
        if s not in cache:
            sinv = inv(s)
            pm = np.array([mul(x, s) for x in range(G)], dtype=np.int64)
            sm = np.array([mul(b, sinv) for b in range(G)], dtype=np.int64)
            cache[s] = (pm, sm)
        return cache[s]

    def cost_of(ds):
        if len({(i, j, s) for i, j, s in ds}) < len(ds):
            return 10 ** 9
        I = np.array([x[0] for x in ds], dtype=np.int64)
        J = np.array([x[1] for x in ds], dtype=np.int64)
        PERM = np.stack([perm_of(x[2])[0] for x in ds])
        SINV = np.stack([perm_of(x[2])[1] for x in ds])
        return _orbit_cost_np(k, G, D, I, J, PERM, SINV)

    cost = cost_of(darts)
    best_cost = cost
    best_darts = [list(x) for x in darts]

    T0 = 3.0
    m = len(darts)
    for t in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.05
        if rng.random() < 0.5:
            # Move 1: re-voltage one dart.
            idx = rng.randrange(m)
            old_s = darts[idx][2]
            darts[idx][2] = rng.randrange(G)
            c2 = cost_of(darts)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                continue
        else:
            # Move 2: swap B-targets of two A-vertices within one layer.
            layer = rng.randrange(d)
            a = layer * k + rng.randrange(k)
            b = layer * k + rng.randrange(k)
            if a == b or darts[a][1] == darts[b][1]:
                continue
            darts[a][1], darts[b][1] = darts[b][1], darts[a][1]
            c2 = cost_of(darts)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[a][1], darts[b][1] = darts[b][1], darts[a][1]
                continue
        if cost < best_cost:
            best_cost = cost
            best_darts = [list(x) for x in darts]

    if best_cost != 0:
        return None
    E = set()
    for i, j, s in best_darts:
        pm = perm_of(s)[0]
        for gg in range(G):
            E.add((i * G + gg, (k + j) * G + int(pm[gg])))
    return 2 * k * G, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 1.0
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
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 3)))
        res = _search(d, D, k, G, rng, 2000, deadline)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
