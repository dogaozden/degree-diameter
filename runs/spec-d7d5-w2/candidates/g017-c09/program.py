import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe exact families (unchanged from the parent).
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
# NEW construction: direct search over d-regular bipartite graphs.
#
# The graph is d perfect matchings ("layers") between side A = {0..h-1} and
# side B = {h..2h-1}. Layers are permutations, so every vertex has degree
# exactly d and the graph is bipartite. Duplicate edges are forbidden.
#
# Moves are edge switches inside one layer (exchange partners of two A
# vertices). The cost is the number of ordered pairs at distance > D,
# computed with packed bitsets (uint64 rows) and numpy.
#
# Simulated annealing runs at a fixed order 2h. A ladder raises h after each
# success and halves the step after each failure. Every candidate is still
# checked with lib.is_valid before it replaces the best graph.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _bad_ordered(nbr, N, D, d):
    """Number of ordered vertex pairs at distance > D, given layer neighbour table nbr (d x N)."""
    W = (N + 63) // 64
    idx = np.arange(N, dtype=np.int64)
    reach = np.zeros((N, W), dtype=np.uint64)
    reach[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        reach = new
    reached = int(_POP8[reach.view(np.uint8)].sum())
    return N * N - reached


def _attempt(d, D, h, rng, deadline):
    """Try to find a d-regular bipartite graph with 2h vertices and diameter <= D. Returns edges or None."""
    N = 2 * h
    M = []
    Minv = []
    cnt = {}
    for _ in range(d):
        pass
    for l in range(d):
        perm = list(range(h))
        rng.shuffle(perm)
        inv = [0] * h
        for a, b in enumerate(perm):
            inv[b] = a
            cnt[(a, b)] = cnt.get((a, b), 0) + 1
        M.append(perm)
        Minv.append(inv)

    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        nbr[l, :h] = h + np.asarray(M[l], dtype=np.int64)
        nbr[l, h:] = np.asarray(Minv[l], dtype=np.int64)

    def swap(l, a1, a2):
        """Exchange the B-partners of A-vertices a1 and a2 in layer l. Calling it twice undoes it."""
        b1 = M[l][a1]
        b2 = M[l][a2]
        cnt[(a1, b1)] -= 1
        cnt[(a2, b2)] -= 1
        cnt[(a1, b2)] = cnt.get((a1, b2), 0) + 1
        cnt[(a2, b1)] = cnt.get((a2, b1), 0) + 1
        M[l][a1] = b2
        M[l][a2] = b1
        Minv[l][b1] = a2
        Minv[l][b2] = a1
        nbr[l, a1] = h + b2
        nbr[l, a2] = h + b1
        nbr[l, h + b2] = a1
        nbr[l, h + b1] = a2

    def dupsum(keys):
        return sum(max(cnt.get(k, 0) - 1, 0) for k in keys)

    # Phase 1: remove duplicate edges with duplicate-non-increasing swaps.
    dup = sum(max(c - 1, 0) for c in cnt.values())
    it = 0
    while dup > 0:
        if time.monotonic() > deadline or it > 400000:
            return None
        it += 1
        l = rng.randrange(d)
        a1, a2 = rng.sample(range(h), 2)
        b1 = M[l][a1]
        b2 = M[l][a2]
        allk = {(a1, b1), (a2, b2), (a1, b2), (a2, b1)}
        before = dupsum(allk)
        swap(l, a1, a2)
        after = dupsum(allk)
        if after > before:
            swap(l, a1, a2)
        else:
            dup += after - before

    # Phase 2: anneal on distance-violation count, keeping the graph simple.
    cur = _bad_ordered(nbr, N, D, d)
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    while cur > 0:
        now = time.monotonic()
        if now > deadline:
            return None
        frac = min(1.0, (now - t_start) / span)
        T = 0.5 + 7.5 * (1.0 - frac)
        l = rng.randrange(d)
        a1, a2 = rng.sample(range(h), 2)
        b1 = M[l][a1]
        b2 = M[l][a2]
        if cnt.get((a1, b2), 0) > 0 or cnt.get((a2, b1), 0) > 0:
            continue
        swap(l, a1, a2)
        new = _bad_ordered(nbr, N, D, d)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            swap(l, a1, a2)

    edges = []
    for l in range(d):
        for a in range(h):
            edges.append((a, h + M[l][a]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
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
            return True
        return False

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Direct search ladder over the order (bold alternative to group lifts).
    if D >= 3 and d >= 2:
        best_h = best_n // 2
        step = max(1, best_h // 8)
        while True:
            now = time.monotonic()
            remaining = deadline - now
            if remaining < 1.0:
                break
            slice_end = min(deadline, now + max(2.0, 0.45 * remaining))
            h_try = best_h + step
            if h_try < 2:
                h_try = 2
            edges = _attempt(d, D, h_try, rng, slice_end)
            if edges is not None and consider(2 * h_try, edges):
                best_h = best_n // 2
            elif edges is not None:
                best_h = best_n // 2
            else:
                step = max(1, step // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
