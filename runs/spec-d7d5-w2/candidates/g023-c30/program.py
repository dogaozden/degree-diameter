import math
import random
import time

import numpy as np

import lib


_POP16 = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Random bipartite d-regular graphs repaired by simulated annealing.
#
# Start from the circulant Haar graph (A_i ~ B_{i+t}), which is d-regular and
# bipartite, then randomise it with 2-switches. A 2-switch replaces edges
# (a1,b1),(a2,b2) by (a1,b2),(a2,b1); it keeps all degrees and the bipartition.
# The cost is the number of unordered vertex pairs at distance > D, computed
# with numpy bitsets. Moves are random switches, or switches aimed at an
# unreached pair. The order is searched by bisection over the side size s.
# ----------------------------------------------------------------------------

def _reach(arr, N, W, D):
    """Bitset per vertex: bit w of row v is set when w lies within distance D of v."""
    idx = np.arange(N, dtype=np.int64)
    R = np.zeros((N, W), dtype=np.uint64)
    R[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = R.copy()
        for t in range(arr.shape[1]):
            new |= R[arr[:, t]]
        if np.array_equal(new, R):
            break
        R = new
    return R


def _cost(R, N):
    """Number of unordered pairs at distance > D."""
    tot = int(_POP16[R.view(np.uint16)].sum())
    return (N * N - tot) // 2


def _row_pc(R, N):
    return _POP16[R.view(np.uint16)].sum(axis=1)


def _anneal(s, d, D, rng, deadline):
    """Try to find a d-regular bipartite graph with s vertices per side and diameter <= D.

    Returns (n, edges) or None if the deadline passes first.
    """
    N = 2 * s
    W = (N + 63) // 64
    arr = np.empty((N, d), dtype=np.int64)
    ar = np.arange(s, dtype=np.int64)
    for t in range(d):
        arr[:s, t] = s + (ar + t) % s      # A_i ~ B_{i+t}
        arr[s:, t] = (ar - t) % s          # B_j ~ A_{j-t}

    def rep(x, old, new):
        row = arr[x]
        arr[x, int(np.argmax(row == old))] = new

    def switch(a1, b1, a2, b2):
        # Replace (a1,b1),(a2,b2) by (a1,b2),(a2,b1). b's are B-indices in 0..s-1.
        B1 = s + b1
        B2 = s + b2
        rep(a1, B1, B2)
        rep(a2, B2, B1)
        rep(B1, a1, a2)
        rep(B2, a2, a1)

    def ok(a1, b1, a2, b2):
        return (a1 != a2 and b1 != b2
                and (s + b2) not in arr[a1] and (s + b1) not in arr[a2])

    def rand_edge_from_a():
        a = rng.randrange(s)
        b = int(arr[a, rng.randrange(d)]) - s
        return a, b

    def edge_at(x):
        y = int(arr[x, rng.randrange(d)])
        return (x, y - s) if x < s else (y, x - s)

    # Mix the circulant into a random-looking regular bipartite graph.
    for _ in range(8 * N):
        a1, b1 = rand_edge_from_a()
        a2, b2 = rand_edge_from_a()
        if ok(a1, b1, a2, b2):
            switch(a1, b1, a2, b2)

    R = _reach(arr, N, W, D)
    cost = _cost(R, N)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        temp = 0.15 + 1.5 * (1.0 - (now - t0) / span)

        if rng.random() < 0.5:
            pc = _row_pc(R, N)
            bad = np.flatnonzero(pc < N)
            if bad.size == 0:
                break
            u = int(bad[rng.randrange(bad.size)])
            bits = np.unpackbits(R[u].view(np.uint8), bitorder="little")[:N]
            miss = np.flatnonzero(bits == 0)
            if miss.size == 0:
                continue
            w = int(miss[rng.randrange(miss.size)])
            e1 = edge_at(u)
            e2 = edge_at(int(arr[w, rng.randrange(d)]))
        else:
            e1 = rand_edge_from_a()
            e2 = rand_edge_from_a()

        a1, b1 = e1
        a2, b2 = e2
        if not ok(a1, b1, a2, b2):
            continue
        switch(a1, b1, a2, b2)
        R2 = _reach(arr, N, W, D)
        c2 = _cost(R2, N)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            R = R2
        else:
            switch(a1, b2, a2, b1)  # undo

    if cost != 0:
        return None
    edges = [(a, int(arr[a, j])) for a in range(s) for j in range(d)]
    return N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
            return True
        return False

    if D == 2:
        return best_n, best_e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best_n, best_e

    if d < 3:
        return best_n, best_e

    rng = random.Random(seed)
    moore_half = max(d, lib.moore_bound(d, D) // 2)
    lo = best_n // 2          # known achievable side size
    hi = None                 # known failing side size
    s = max(lo + 1, int(0.365 * moore_half) + 2)

    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 1.0:
            break
        if s <= lo:
            s = lo + 1
        if hi is not None and s >= hi:
            break

        slice_end = now + remaining * 0.5
        res = _anneal(s, d, D, rng, min(slice_end, deadline))
        if res is not None and consider(res[0], res[1]):
            lo = s
            if hi is None:
                s = s + max(1, s // 100)
            else:
                s = (lo + hi) // 2
        else:
            hi = s
            s = (lo + hi) // 2

        if hi is not None and hi - lo <= 1:
            break

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
