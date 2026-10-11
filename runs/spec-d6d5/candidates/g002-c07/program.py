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
# Group-voltage lifts over semidirect products.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h, for base size k.
# Dart (i, j, s) joins A_i,g to B_j,g*s for every g in the group.
# Each layer is a permutation of the base, so every vertex has degree d.
#
# NEW HELPER: source-bitmask reachability.
# Instead of one BFS per representative, every vertex v carries an integer
# bitmask M[v] whose bit r is set when representative r is within distance t
# of v. One sweep over all edges advances every representative at once:
#     M_{t+1}[v] = M_t[v] OR (OR of M_t[u] for u adjacent to v).
# Left multiplication by the group is an automorphism, so reaching all
# vertices from the 2k representatives is equivalent to diameter <= D.
# The cost is the number of zero bits, and witnesses are the vertices with
# a zero bit. Witness-guided moves re-voltage a dart touching the base class
# of a witness, and uniform moves are kept with probability 0.3.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
_WITNESS_CAP = 40


def _popcount(x):
    return bin(x).count("1")


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
    """Bitmask-parallel reachability. Returns (missing, witnesses).

    missing: number of (representative, vertex) pairs not reached within D steps.
    witnesses: up to _WITNESS_CAP vertices that some representative misses.
    """
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG, []
    N = 2 * k * G
    nb = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            nb[a].append(b)
            nb[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    R = len(reps)
    M = [0] * N
    for r_idx, src in enumerate(reps):
        M[src] |= 1 << r_idx
    for _ in range(D):
        newM = [0] * N
        for v in range(N):
            x = M[v]
            for u in nb[v]:
                x |= M[u]
            newM[v] = x
        if newM == M:
            break
        M = newM
    full = (1 << R) - 1
    missing = 0
    witnesses = []
    for v in range(N):
        miss = full & ~M[v]
        if miss:
            missing += _popcount(miss)
            if len(witnesses) < _WITNESS_CAP:
                witnesses.append(v)
    return missing, witnesses


def _pick_dart(darts, witnesses, k, G, rng):
    """Witness-guided choice of the dart to re-voltage (uniform with prob 0.3)."""
    if witnesses and rng.random() < 0.7:
        w = rng.choice(witnesses)
        cls = w // G
        if cls < k:
            cand = [t for t, (i, _j, _s) in enumerate(darts) if i == cls]
        else:
            cand = [t for t, (_i, j, _s) in enumerate(darts) if j == cls - k]
        if cand:
            return rng.choice(cand)
    return rng.randrange(len(darts))


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _search(d, D, k, G, rng, iters, deadline):
    """Simulated annealing over voltages in a group of order about G.

    Returns (n, edges) with diameter <= D, or None.
    """
    g = _sample_group(G, rng)
    if g is None:
        return None
    G, mul = g[0], g[1]
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = []
    for p in layers:
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost, witnesses = _cost(k, G, D, darts, perms)

    best_cost = cost
    best_darts = [list(x) for x in darts]
    best_perms = list(perms)

    T0 = 3.0
    for t in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.05
        idx = _pick_dart(darts, witnesses, k, G, rng)
        old_s = darts[idx][2]
        old_perm = perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = _right_perm(mul, G, new_s)
        c2, w2 = _cost(k, G, D, darts, perms)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            witnesses = w2
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
    # Stay well inside the limit: use at most 85% and leave at least 3 seconds spare.
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
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

    # Calibration cases that already meet the Moore bound return immediately.
    moore = lib._moore_bound(d, D)
    if best_n >= moore:
        return best

    # Main search: bitmask-cost annealing over group voltage lifts.
    # Group orders are targeted just above the current best, with a narrow spread.
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 10 + 1)))
        res = _search(d, D, k, G, rng, 3000, deadline)
        if res is not None:
            consider(res[0], res[1])
        if best_n >= moore:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
