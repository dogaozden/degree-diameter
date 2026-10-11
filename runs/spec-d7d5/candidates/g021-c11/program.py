import math
import random
import time

import numpy as np

import lib

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_ITERS = 2500


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _cost(A, B, D):
    """Number of ordered vertex pairs at distance > D in the bipartite graph.

    A[i, p] is the local B-index of the p-th neighbour of A-vertex i;
    B[j, p] is the local A-index of the p-th neighbour of B-vertex j.
    Full ids: A-vertex i -> i, B-vertex j -> S + j.
    """
    S, d = A.shape
    N = 2 * S
    full = np.concatenate([S + A, B], axis=0)
    W = (N + 63) // 64
    R = np.zeros((N, W), dtype=np.uint64)
    idx = np.arange(N, dtype=np.int64)
    R[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = R.copy()
        for p in range(d):
            new |= R[full[:, p]]
        if np.array_equal(new, R):
            break
        R = new
    pop = int(_POP8[R.view(np.uint8)].sum())
    return N * N - pop


def _switch(A, B, a1, p1, nb1, a2, p2, nb2, b1, q1, na1, b2, q2, na2):
    A[a1, p1] = nb1
    A[a2, p2] = nb2
    B[b1, q1] = na1
    B[b2, q2] = na2


def _anneal(A, B, D, rng, deadline, iters):
    """Degree-preserving edge-switch annealing. Returns the final cost (0 means valid)."""
    S, d = A.shape
    cost = _cost(A, B, D)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        a1 = rng.randrange(S)
        a2 = rng.randrange(S)
        if a1 == a2:
            continue
        p1 = rng.randrange(d)
        p2 = rng.randrange(d)
        b1 = int(A[a1, p1])
        b2 = int(A[a2, p2])
        if b1 == b2 or (A[a1] == b2).any() or (A[a2] == b1).any():
            continue
        q1 = int(np.flatnonzero(B[b1] == a1)[0])
        q2 = int(np.flatnonzero(B[b2] == a2)[0])
        _switch(A, B, a1, p1, b2, a2, p2, b1, b1, q1, a2, b2, q2, a1)
        c2 = _cost(A, B, D)
        T = max(0.4, 3.0 * (1.0 - t / iters))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _switch(A, B, a1, p1, b1, a2, p2, b2, b1, q1, a1, b2, q2, a2)
    return cost


def _extend(A, B, t, d, rng):
    """Add t new A-vertices and t new B-vertices, each of degree d, by edge surgery.

    Old degrees are preserved: each surgery removes an edge (a, b) and adds (a, y), (x, b).
    Returns (A2, B2) or None.
    """
    S = A.shape[0]
    S2 = S + t
    A2 = np.full((S2, d), -1, dtype=np.int64)
    B2 = np.full((S2, d), -1, dtype=np.int64)
    A2[:S] = A
    B2[:S] = B
    for k in range(t):
        x = S + k
        y = S + k
        pool = S + k
        xs, ys = set(), set()
        cnt = 0
        tries = 0
        while cnt < d:
            tries += 1
            if tries > 100000:
                return None
            a = rng.randrange(pool)
            p = rng.randrange(d)
            b = int(A2[a, p])
            if b in xs or a in ys:
                continue
            q = int(np.flatnonzero(B2[b] == a)[0])
            A2[a, p] = y
            B2[y, cnt] = a
            B2[b, q] = x
            A2[x, cnt] = b
            xs.add(b)
            ys.add(a)
            cnt += 1
    return A2, B2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 6.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    rng = random.Random(seed)
    A = np.tile(np.arange(d, dtype=np.int64), (d, 1))
    B = A.copy()

    step = 1
    fails = 0
    while time.monotonic() < deadline - 0.5 and fails < 10:
        ext = _extend(A, B, step, d, rng)
        if ext is None:
            step = max(1, step // 2)
            fails += 1
            continue
        A2, B2 = ext
        cost = _anneal(A2, B2, D, rng, deadline, _ITERS)
        if cost == 0:
            A, B = A2, B2
            step = min(step * 2, 32)
            fails = 0
        else:
            step = max(1, step // 2)
            fails += 1

    S = A.shape[0]
    if 2 * S > best[0]:
        edges = [(a, S + int(A[a, p])) for a in range(S) for p in range(d)]
        consider(2 * S, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
