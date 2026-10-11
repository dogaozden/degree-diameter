import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Strategy
#
# Exact fallbacks first: K_{d,d} (valid for D >= 2) and PG(2,q) for D = 3.
# For D >= 3 and d >= 3, an unstructured search is used instead of a lift:
#   * a d-regular bipartite graph is kept as two (h x d) neighbour tables;
#   * edge switches (exchange two edges' B-endpoints) keep it d-regular and
#     bipartite, and simulated annealing drives the number of pairs at
#     distance > D to zero;
#   * once a valid graph is found, the order grows by one pair per side
#     (remove d-1 edges with distinct endpoints, attach a new A-vertex and
#     B-vertex) and annealing repairs the result.
# Each step is validated by lib.is_valid at checkpoints; the largest valid
# checkpoint is returned, with K_{d,d} as the final fallback.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 30), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _global(NA, NB):
    """Global neighbour table: A-vertices 0..h-1, B-vertices h..2h-1."""
    h = NA.shape[0]
    return np.concatenate([NA + h, NB], axis=0)


def _cost(N, n, D):
    """Number of ordered pairs (v, w) with distance > D, via bitset balls."""
    W = (n + 63) // 64
    reach = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n, dtype=np.int64)
    reach[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(D):
        new = reach | np.bitwise_or.reduce(reach[N], axis=1)
        if np.array_equal(new, reach):
            break
        reach = new
    total = int(_POP8[reach.view(np.uint8)].sum())
    return n * n - total


def _switch(NA, NB, rng):
    """Exchange B-endpoints of two random A-edges. Returns undo info or None."""
    h, d = NA.shape
    a1, a2 = rng.randrange(h), rng.randrange(h)
    if a1 == a2:
        return None
    s1, s2 = rng.randrange(d), rng.randrange(d)
    b1, b2 = int(NA[a1, s1]), int(NA[a2, s2])
    if b1 == b2 or (NA[a1] == b2).any() or (NA[a2] == b1).any():
        return None
    saved = (a1, a2, b1, b2, NA[a1].copy(), NA[a2].copy(), NB[b1].copy(), NB[b2].copy())
    NA[a1, s1] = b2
    NA[a2, s2] = b1
    j1 = int(np.flatnonzero(NB[b1] == a1)[0])
    j2 = int(np.flatnonzero(NB[b2] == a2)[0])
    NB[b1, j1] = a2
    NB[b2, j2] = a1
    return saved


def _undo(NA, NB, sv):
    a1, a2, b1, b2, ra1, ra2, rb1, rb2 = sv
    NA[a1] = ra1
    NA[a2] = ra2
    NB[b1] = rb1
    NB[b2] = rb2


def _anneal(NA, NB, D, rng, deadline, iters, T0):
    """Simulated annealing over switches. Modifies NA, NB in place; True if cost reaches 0."""
    h = NA.shape[0]
    cost = _cost(_global(NA, NB), 2 * h, D)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 0.3 + T0 * (1.0 - t / iters)
        sv = _switch(NA, NB, rng)
        if sv is None:
            continue
        c2 = _cost(_global(NA, NB), 2 * h, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _undo(NA, NB, sv)
    return cost == 0


def _grow(NA, NB, rng):
    """Add one A-vertex and one B-vertex (joined to each other). Returns new copies or None."""
    h, d = NA.shape
    cand = [(a, s) for a in range(h) for s in range(d)]
    rng.shuffle(cand)
    usedA, usedB = set(), set()
    chosen = []
    for a, s in cand:
        b = int(NA[a, s])
        if a in usedA or b in usedB:
            continue
        chosen.append((a, s, b))
        usedA.add(a)
        usedB.add(b)
        if len(chosen) == d - 1:
            break
    if len(chosen) < d - 1:
        return None
    x = h
    y = h
    newA = np.zeros((h + 1, d), dtype=np.int64)
    newB = np.zeros((h + 1, d), dtype=np.int64)
    newA[:h] = NA
    newB[:h] = NB
    for i, (a, s, b) in enumerate(chosen):
        newA[a, s] = y                      # a_i loses b_i, gains y
        j = int(np.flatnonzero(newB[b] == a)[0])
        newB[b, j] = x                      # b_i loses a_i, gains x
        newA[x, i] = b                      # x ~ b_i
        newB[y, i] = a                      # y ~ a_i
    newA[x, d - 1] = y
    newB[y, d - 1] = x
    return newA, newB


def _search(d, D, seed, deadline):
    """Grow a d-regular bipartite graph of diameter <= D. Returns a validated (n, edges) or None."""
    rng = random.Random(seed)
    moore = lib.moore_bound(d, D)
    h = max(d, int(0.22 * moore / 2))
    ar = np.arange(h, dtype=np.int64)
    NA = np.empty((h, d), dtype=np.int64)
    NB = np.empty((h, d), dtype=np.int64)
    for l in range(d):
        NA[:, l] = (ar + l) % h
        NB[:, l] = (ar - l) % h

    def checkpoint(A, B):
        hh = A.shape[0]
        e = [(a, hh + int(b)) for a in range(hh) for b in A[a]]
        if lib.is_valid(2 * hh, e, d, D):
            return (2 * hh, e)
        return None

    if not _anneal(NA, NB, D, rng, deadline, 20000, 4.0):
        return None
    best = checkpoint(NA, NB)
    cur = (NA, NB)
    steps = 0
    while time.monotonic() < deadline:
        grown = False
        for _ in range(4):
            res = _grow(cur[0], cur[1], rng)
            if res is None:
                break
            A, B = res
            if _anneal(A, B, D, rng, deadline, 500, 2.0):
                cur = (A, B)
                grown = True
                break
        if not grown:
            break
        steps += 1
        if steps % 20 == 0:
            cp = checkpoint(*cur)
            if cp is not None and (best is None or cp[0] > best[0]):
                best = cp
    cp = checkpoint(*cur)
    if cp is not None and (best is None or cp[0] > best[0]):
        best = cp
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.80 * time_limit, time_limit - 8.0))
    deadline = t0 + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 3:
        pg = _pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best_n, best_e

    if d >= 3 and D >= 3 and time.monotonic() < deadline:
        try:
            res = _search(d, D, seed, deadline)
        except Exception:
            res = None
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
