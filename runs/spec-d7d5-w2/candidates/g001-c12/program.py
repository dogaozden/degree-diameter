import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact and algebraic constructions (kept from the parent as fallbacks).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power >= 3, else None."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
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
# New main search: edge-switch annealing on bipartite d-regular graphs.
#
# Replaces the bi-Cayley lift search. A graph on n = 2h vertices (h per side)
# starts as a circulant d-regular bipartite graph, is shuffled by random
# switches, then annealed: a switch replaces edges (a1,b1),(a2,b2) with
# (a1,b2),(a2,b1), which keeps every degree fixed. The cost is the number of
# ordered vertex pairs at distance more than D, computed with packed bitsets
# in numpy. Zero cost means the diameter is at most D.
#
# Order is grown adaptively: a bracketing search on h, where each success
# doubles the step and each failure halves it.
# ----------------------------------------------------------------------------

_POP16 = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _anneal(d, D, h, rng, slice_end):
    """Try to find a d-regular bipartite graph with h + h vertices and diameter <= D.

    Returns (n, edges) on success, or None if the time slice ends first.
    """
    n = 2 * h
    W = (n + 63) // 64
    E = h * d
    M = np.zeros((h, h), dtype=bool)
    EA = np.empty(E, dtype=np.int64)
    EB = np.empty(E, dtype=np.int64)
    nbr = np.empty((n, d), dtype=np.int64)

    # Circulant start: A_i ~ B_{(i+s) mod h} for s = 0..d-1 (needs h >= d).
    for i in range(h):
        for s in range(d):
            b = (i + s) % h
            M[i, b] = True
            EA[i * d + s] = i
            EB[i * d + s] = b
            nbr[i, s] = h + b
    for b in range(h):
        for s in range(d):
            nbr[h + b, s] = (b - s) % h

    def _switch(e1, e2):
        """Replace (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Returns False if the switch is illegal."""
        a1 = int(EA[e1]); b1 = int(EB[e1])
        a2 = int(EA[e2]); b2 = int(EB[e2])
        if a1 == a2 or b1 == b2 or M[a1, b2] or M[a2, b1]:
            return False
        M[a1, b1] = False
        M[a2, b2] = False
        M[a1, b2] = True
        M[a2, b1] = True
        j = int(np.flatnonzero(nbr[a1] == h + b1)[0])
        nbr[a1, j] = h + b2
        j = int(np.flatnonzero(nbr[a2] == h + b2)[0])
        nbr[a2, j] = h + b1
        j = int(np.flatnonzero(nbr[h + b1] == a1)[0])
        nbr[h + b1, j] = a2
        j = int(np.flatnonzero(nbr[h + b2] == a2)[0])
        nbr[h + b2, j] = a1
        EA[e1] = a1; EB[e1] = b2
        EA[e2] = a2; EB[e2] = b1
        return True

    # Mix the circulant start with random legal switches (no cost evaluation).
    for _ in range(4 * E):
        e1 = rng.randrange(E)
        e2 = rng.randrange(E)
        if e1 != e2:
            _switch(e1, e2)

    idx = np.arange(n, dtype=np.int64)
    init = np.zeros((n, W), dtype=np.uint64)
    init[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))

    def cost_fn():
        """Ordered pairs at distance > D (zero iff diameter <= D)."""
        reach = init.copy()
        for _ in range(D):
            new = reach.copy()
            for j in range(d):
                new |= reach[nbr[:, j]]
            if np.array_equal(new, reach):
                break
            reach = new
        return n * n - int(_POP16[reach.view(np.uint16)].sum())

    def build_graph():
        rows, cols = np.nonzero(M)
        return n, [(int(a), h + int(b)) for a, b in zip(rows, cols)]

    cost = cost_fn()
    if cost == 0:
        return build_graph()

    T0 = max(2.0, 0.02 * cost)
    t0 = time.monotonic()
    span = max(1e-3, slice_end - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= slice_end:
            break
        frac = (now - t0) / span
        temp = T0 * (1e-4 ** frac)
        e1 = rng.randrange(E)
        e2 = rng.randrange(E)
        if e1 == e2 or not _switch(e1, e2):
            continue
        c2 = cost_fn()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / max(temp, 1e-9)):
            cost = c2
        else:
            _switch(e1, e2)  # the reverse switch restores the previous graph

    if cost != 0:
        return None
    return build_graph()


def _grow(d, D, rng, deadline, consider, h0):
    """Bracketing search on h: find the largest h for which _anneal succeeds in its slice."""
    h_ok = h0
    step = max(1, h0 // 3)
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        h_try = h_ok + step
        slice_end = time.monotonic() + max(1.0, min(remaining, 0.35 * remaining))
        res = _anneal(d, D, h_try, rng, min(slice_end, deadline))
        if res is not None:
            consider(res[0], res[1])
            h_ok = h_try
            step = step * 2
        else:
            step = max(1, step // 2)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.9 * time_limit, time_limit - 5.0))
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

    # Exact constructions. Return immediately for calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 3:
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: edge-switch annealing, grown from the best graph found so far.
    if d >= 3 and time.monotonic() < deadline:
        h0 = max(d, best_n // 2)
        _grow(d, D, rng, deadline, consider, h0)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
