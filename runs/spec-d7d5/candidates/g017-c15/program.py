import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / algebraic families (kept from the parent as safe baselines).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph (degree q+2 <= d) for the largest prime power q <= d-2, or None."""
    for q in range(d - 2, 2, -1):
        if lib.is_prime_power(q):
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
# New family: random d-regular bipartite graphs (union of d perfect matchings
# between two sides of size n), repaired by simulated annealing on the number
# of ordered vertex pairs at distance > D. This replaces the parent's bi-Cayley
# lifts, which were limited by group structure.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _reach_bits(N, nbr, D):
    """Packed reachability: bit w of row v is set iff dist(v, w) <= D."""
    W = (N + 63) // 64
    idx = np.arange(N, dtype=np.int64)
    reach = np.zeros((N, W), dtype=np.uint64)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for l in range(nbr.shape[0]):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _try_regular(n, d, D, g, rng, deadline, PEN=50):
    """Search for a d-regular bipartite graph with n vertices per side and diameter <= D.

    Returns (N, edges) on success, None on timeout.
    """
    N = 2 * n
    perm = np.empty((d, n), dtype=np.int64)
    inv = np.empty((d, n), dtype=np.int64)
    for l in range(d):
        perm[l] = g.permutation(n)
        inv[l, perm[l]] = np.arange(n)
    nbr = np.empty((d, N), dtype=np.int64)
    nbr[:, :n] = n + perm
    nbr[:, n:] = inv

    def swap(l, a1, a2):
        """Exchange the B-partners of A-vertices a1, a2 in layer l. Applying it twice is identity."""
        p1, p2 = perm[l, a1], perm[l, a2]
        perm[l, a1], perm[l, a2] = p2, p1
        inv[l, p2] = a1
        inv[l, p1] = a2
        nbr[l, a1] = n + p2
        nbr[l, a2] = n + p1
        nbr[l, n + p2] = a1
        nbr[l, n + p1] = a2

    def dups():
        S = np.sort(perm.T, axis=1)
        return int(np.count_nonzero(S[:, 1:] == S[:, :-1]))

    def evaluate():
        reach = _reach_bits(N, nbr, D)
        counts = _POP8[reach.view(np.uint8)].sum(axis=1)
        unreached = N * N - int(counts.sum())
        return unreached + PEN * dups(), counts, reach

    cost, counts, reach = evaluate()
    T0 = 20.0
    t0 = time.monotonic()
    span = max(0.5, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        temp = 0.5 + T0 * max(0.0, 1.0 - (now - t0) / span)
        l = int(g.integers(d))
        if rng.random() < 0.5:
            # Defect-targeted: pick a vertex with unreached partners, act on its layer-l edge.
            bad = np.flatnonzero(counts < N)
            if bad.size:
                u = int(bad[rng.randrange(bad.size)])
                a1 = u if u < n else int(inv[l, u - n])
            else:
                a1 = rng.randrange(n)
        else:
            a1 = rng.randrange(n)
        a2 = rng.randrange(n)
        if a1 == a2:
            continue
        swap(l, a1, a2)
        c2, cnt2, r2 = evaluate()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, counts, reach = c2, cnt2, r2
        else:
            swap(l, a1, a2)

    edges = [(a, n + int(perm[l, a])) for l in range(d) for a in range(n)]
    return N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)
    g = np.random.default_rng(abs(int(seed)) % (1 << 32))

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        m = 2 * D
        return m, [(i, (i + 1) % m) for i in range(m)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 3:
        if lib.is_prime_power(d - 1):
            return best
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
        return best
    if D >= 4:
        gq = _best_gq(d) if D == 4 else None
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: bisection on the number of vertices per side of a random
    # d-regular bipartite graph repaired towards diameter <= D.
    per_side_moore = sum((d - 1) ** i for i in range(D))
    lo = max(d, best_n // 2)
    hi = per_side_moore + 1
    guess = min(hi - 1, max(lo + 1, 400))
    while time.monotonic() < deadline - 0.5 and hi - lo > 1:
        n = min(max(guess, lo + 1), hi - 1)
        remaining = deadline - time.monotonic()
        sub_deadline = min(deadline, time.monotonic() + max(2.0, 0.4 * remaining))
        res = _try_regular(n, d, D, g, rng, sub_deadline)
        if res is not None:
            consider(res[0], res[1])
            lo = n
        else:
            hi = n
        guess = (lo + hi) // 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
