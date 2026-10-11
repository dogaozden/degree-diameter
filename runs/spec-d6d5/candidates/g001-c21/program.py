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
# Every vertex has degree exactly d (one dart per layer), and the lift is
# invariant under left multiplication, so diameter <= D only needs checking
# from the 2k representatives.
#
# New helper: the reachability check is vectorized with numpy. All 2k
# representatives are advanced together with one fancy-indexed boolean
# operation per BFS round on a fixed (N, d) neighbour matrix. This makes each
# cost evaluation several times cheaper than list-based BFS, so the annealing
# gets many more moves within the time budget.
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


def _right_perm(mul, G, s, cache):
    """Permutation g -> g*s of the group as an int64 array, memoized per s."""
    p = cache.get(s)
    if p is None:
        p = np.fromiter((mul(g, s) for g in range(G)), dtype=np.int64, count=G)
        cache[s] = p
    return p


def _build_nbr(k, G, d, darts, perms):
    """Return the (2kG, d) neighbour matrix of the lift, or None if some vertex overflows degree d."""
    N = 2 * k * G
    nbr = np.empty((N, d), dtype=np.int64)
    cntA = [0] * k
    cntB = [0] * k
    ga = np.arange(G, dtype=np.int64)
    for (i, j, _), pm in zip(darts, perms):
        if cntA[i] >= d or cntB[j] >= d:
            return None
        sa = cntA[i]
        cntA[i] += 1
        sb = cntB[j]
        cntB[j] += 1
        b_idx = (k + j) * G + pm
        nbr[i * G:(i + 1) * G, sa] = b_idx
        nbr[b_idx, sb] = i * G + ga
    return nbr


def _cost_nbr(k, G, D, nbr):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    N = nbr.shape[0]
    R = 2 * k
    reps = np.array([i * G for i in range(k)] + [(k + j) * G for j in range(k)], dtype=np.int64)
    reach = np.zeros((R, N), dtype=bool)
    reach[np.arange(R), reps] = True
    for _ in range(D):
        nxt = reach | reach[:, nbr].any(axis=2)
        if np.array_equal(nxt, reach):
            break
        reach = nxt
    return R * N - int(reach.sum())


def _evaluate(k, G, d, D, darts, perms):
    """Return (cost, nbr). Duplicate darts or degree overflow give a huge cost."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG, None
    nbr = _build_nbr(k, G, d, darts, perms)
    if nbr is None:
        return _BIG, None
    return _cost_nbr(k, G, D, nbr), nbr


def _edges_from(k, G, nbr):
    """Convert a neighbour matrix to (n, edges); A-vertices are 0..kG-1, so each edge is listed once."""
    NA = k * G
    rows = np.repeat(np.arange(NA, dtype=np.int64), nbr.shape[1])
    cols = nbr[:NA].ravel()
    return 2 * NA, list(zip(rows.tolist(), cols.tolist()))


def _search(d, D, k, G, mul, rng, end):
    """Simulated annealing over voltages in a group of order G, until time `end`.

    Returns (n, edges) with diameter <= D, or None.
    """
    cache = {}
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, p[i], rng.randrange(G)] for p in layers for i in range(k)]
    perms = [_right_perm(mul, G, s, cache) for _, _, s in darts]
    cost, _ = _evaluate(k, G, d, D, darts, perms)

    best_cost = cost
    best_state = ([list(x) for x in darts], list(perms))

    t0 = time.monotonic()
    span = max(1e-6, end - t0)
    T0 = 2.0
    while best_cost > 0:
        now = time.monotonic()
        if now >= end:
            break
        T = T0 * (1.0 - (now - t0) / span) + 0.05
        idx = rng.randrange(len(darts))
        old_s, old_p = darts[idx][2], perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = _right_perm(mul, G, new_s, cache)
        c2, _ = _evaluate(k, G, d, D, darts, perms)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_state = ([list(x) for x in darts], list(perms))
        else:
            darts[idx][2] = old_s
            perms[idx] = old_p

    if best_cost == 0:
        bd, bp = best_state
        _, nbr = _evaluate(k, G, d, D, bd, bp)
        if nbr is not None:
            return _edges_from(k, G, nbr)
    return None


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

    # Already at the Moore bound: nothing can beat it, so return immediately.
    if best_n >= lib._moore_bound(d, D):
        return best

    # Main search: annealed group voltage lifts with 1-3 base vertices per side.
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = max(1, best_n // (2 * k))
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            break
        budget = min(4.0, remaining)
        res = _search(d, D, k, order, mul, rng, time.monotonic() + budget)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
