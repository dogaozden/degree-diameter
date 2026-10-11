import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / safe constructions (kept from the parent as fallbacks).
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
# New construction family: simulated annealing over d-regular bipartite graphs.
#
# A bipartite graph on sides A = {0..s-1}, B = {s..2s-1} is stored as
#   nA[a, :] = B-indices (0..s-1) adjacent to a,
#   nB[b, :] = A-indices adjacent to b.
# Starting point: a circulant Haar-type graph (simple, d-regular).
# Moves: double-edge swaps (keep d-regularity and simplicity).
# Cost: number of ordered (vertex, vertex) pairs at distance > D, computed
# with bit-packed reach sets in numpy. Annealing accepts worsening moves
# with a temperature that decays over the attempt.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _full_nbr(nA, nB, s):
    """Full neighbour table (2s, d): rows 0..s-1 are A-vertices, rows s..2s-1 are B-vertices."""
    return np.vstack([nA + s, nB])


def _cost(nbr, n, D):
    """Number of ordered pairs (u, v) with dist(u, v) > D, computed by bit-packed BFS-style reach."""
    W = (n + 63) // 64
    idx = np.arange(n)
    reach = np.zeros((n, W), dtype=np.uint64)
    reach[idx, idx >> 6] = np.ones(n, dtype=np.uint64) << (idx & 63).astype(np.uint64)
    for _ in range(D):
        new = reach.copy()
        for j in range(nbr.shape[1]):
            new |= reach[nbr[:, j]]
        if np.array_equal(new, reach):
            break
        reach = new
    pop = int(_POP8[reach.view(np.uint8)].sum())
    return n * n - pop


def _try_swap(nA, nB, rng, d):
    """Propose a double-edge swap. Returns the move record, or None if it is not allowed."""
    s = nA.shape[0]
    a1 = rng.randrange(s)
    a2 = rng.randrange(s)
    if a1 == a2:
        return None
    x = rng.randrange(d)
    y = rng.randrange(d)
    b1 = int(nA[a1, x])
    b2 = int(nA[a2, y])
    if (nA[a1] == b2).any() or (nA[a2] == b1).any():
        return None
    nA[a1, x] = b2
    nA[a2, y] = b1
    nB[b1][int(np.argmax(nB[b1] == a1))] = a2
    nB[b2][int(np.argmax(nB[b2] == a2))] = a1
    return (a1, a2, x, y, b1, b2)


def _undo(nA, nB, mv):
    """Reverse a move produced by _try_swap."""
    a1, a2, x, y, b1, b2 = mv
    nA[a1, x] = b1
    nA[a2, y] = b2
    nB[b1][int(np.argmax(nB[b1] == a2))] = a1
    nB[b2][int(np.argmax(nB[b2] == a1))] = a2


def _anneal(s, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph with s vertices per side. Returns (n, edges) or None."""
    shifts = np.array(rng.sample(range(s), d), dtype=np.int64)
    nA = (np.arange(s, dtype=np.int64)[:, None] + shifts[None, :]) % s
    nB = np.empty((s, d), dtype=np.int64)
    fill = np.zeros(s, dtype=np.int64)
    for a in range(s):
        for b in nA[a]:
            b = int(b)
            nB[b, fill[b]] = a
            fill[b] += 1

    # Randomise the starting graph without tracking cost.
    for _ in range(3 * s * d):
        _try_swap(nA, nB, rng, d)

    n = 2 * s
    nbr = _full_nbr(nA, nB, s)
    cost = _cost(nbr, n, D)
    T0 = 4.0
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cost > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - start) / span
        T = 0.05 + T0 * (1.0 - frac)
        mv = _try_swap(nA, nB, rng, d)
        if mv is None:
            continue
        nbr = _full_nbr(nA, nB, s)
        c2 = _cost(nbr, n, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _undo(nA, nB, mv)

    if cost != 0:
        return None
    edges = []
    for a in range(s):
        for b in nA[a]:
            edges.append((a, s + int(b)))
    return n, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.92 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

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

    if D == 2 or d < 3:
        return best

    # Annealing over d-regular bipartite graphs, growing the side size.
    s_max = min(1500, lib.moore_bound(d, D) // 2)
    step = max(1, best_n // 2 // 40)
    while time.monotonic() < deadline:
        if best_n // 2 >= s_max:
            break
        s_try = min(s_max, max(d, best_n // 2 + step))
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.5:
            break
        attempt_deadline = min(deadline, now + max(3.0, 0.5 * remaining))
        res = _anneal(s_try, d, D, rng, attempt_deadline)
        if res is not None:
            consider(res[0], res[1])
            step = max(1, int(step * 1.5))
        elif step > 1:
            step = max(1, step // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
