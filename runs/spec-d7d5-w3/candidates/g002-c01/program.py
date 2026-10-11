import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact or known constructions (used only where they apply).
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
# New family: unstructured random biregular bipartite graphs repaired by
# simulated annealing on double-edge switches. The objective is the number
# of ordered vertex pairs at distance > D, computed with packed bitsets.
# ----------------------------------------------------------------------------

_POP16 = None


def _pop16():
    """Popcount table for 16-bit values."""
    global _POP16
    if _POP16 is None:
        x = np.arange(1 << 16, dtype=np.int64)
        t = np.zeros(1 << 16, dtype=np.int64)
        for b in range(16):
            t += (x >> b) & 1
        _POP16 = t
    return _POP16


def _cost(nbr, N, D, pop):
    """Number of ordered pairs (u, v) with dist(u, v) > D, for adjacency array nbr of shape (N, d)."""
    W = (N + 63) // 64
    idx = np.arange(N)
    reach = np.zeros((N, W), dtype=np.uint64)
    reach[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(D):
        new = reach | np.bitwise_or.reduce(reach[nbr], axis=1)
        if np.array_equal(new, reach):
            break
        reach = new
    total = int(pop[reach.view(np.uint16)].sum())
    return N * N - total


def _init_graph(M, d, rng):
    """Random d-regular bipartite multigraph-free edge list on parts of size M.

    Returns (ea, eb) arrays of length M*d, or None if repair failed.
    Edge e joins A-vertex ea[e] with B-vertex eb[e] (both 0..M-1).
    """
    ea = np.repeat(np.arange(M, dtype=np.int64), d)
    eb = np.empty(M * d, dtype=np.int64)
    view = eb.reshape(M, d)
    for layer in range(d):
        perm = np.array(rng.sample(range(M), M), dtype=np.int64)
        if layer > 0:
            prev = view[:, :layer]
            for _ in range(20000):
                bad = np.flatnonzero((prev == perm[:, None]).any(axis=1))
                if bad.size == 0:
                    break
                x = int(bad[rng.randrange(bad.size)])
                y = rng.randrange(M)
                perm[x], perm[y] = perm[y], perm[x]
            else:
                return None
        view[:, layer] = perm
    return ea, eb


def _nbr(ea, eb, M, d):
    """Build the (2M, d) neighbour array; A-vertices are 0..M-1, B-vertices are M..2M-1."""
    oa = np.argsort(ea, kind="stable")
    ob = np.argsort(eb, kind="stable")
    nA = eb[oa].reshape(M, d) + M
    nB = ea[ob].reshape(M, d)
    return np.vstack([nA, nB])


def _anneal(M, d, D, rng, deadline, pop):
    """Anneal a random d-regular bipartite graph on 2M vertices to diameter <= D.

    Returns (ea, eb) on success, or None on timeout.
    """
    init = _init_graph(M, d, rng)
    if init is None:
        return None
    ea, eb = init
    N = 2 * M
    E = M * d
    S = set((ea * M + eb).tolist())
    cur = _cost(_nbr(ea, eb, M, d), N, D, pop)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now > deadline:
            return None
        e1 = rng.randrange(E)
        e2 = rng.randrange(E)
        a1 = int(ea[e1])
        b1 = int(eb[e1])
        a2 = int(ea[e2])
        b2 = int(eb[e2])
        if a1 == a2 or b1 == b2:
            continue
        k1 = a1 * M + b2
        k2 = a2 * M + b1
        if k1 in S or k2 in S:
            continue
        eb[e1] = b2
        eb[e2] = b1
        new = _cost(_nbr(ea, eb, M, d), N, D, pop)
        frac = (now - start) / span
        temp = max(0.5, 0.002 * cur * (1.0 - frac))
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
            S.discard(a1 * M + b1)
            S.discard(a2 * M + b2)
            S.add(k1)
            S.add(k2)
        else:
            eb[e1] = b1
            eb[e2] = b2
    return ea, eb


def _random_search(d, D, deadline, rng):
    """Search for the largest M (order 2M) with a valid random biregular graph.

    Geometric growth, then bisection on failure. Returns (M, ea, eb) or None.
    """
    pop = _pop16()
    moore = lib.moore_bound(d, D)
    lo = d                      # K_{d,d} is always valid for D >= 2
    hi = moore // 2 + 1         # any M above this exceeds the Moore bound
    best = None
    cand = max(d + 1, int(lo * 1.5))
    while time.monotonic() < deadline and lo + 1 < hi:
        remaining = deadline - time.monotonic()
        if cand >= hi or cand <= lo:
            cand = (lo + hi) // 2
        if cand <= lo:
            break
        cap = min(remaining, max(4.0, 0.3 * remaining))
        res = _anneal(cand, d, D, rng, time.monotonic() + cap, pop)
        if res is not None:
            lo = cand
            best = (cand, res[0], res[1])
            cand = int(cand * 1.15) + 1 if hi > cand * 1.15 else (lo + hi) // 2
        else:
            hi = cand
            cand = (lo + hi) // 2
        if hi - lo <= max(1, lo // 200):
            break
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Cycle C_{2D} is bipartite, 2-regular, and has diameter D.
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions for small D.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ar = lib.araujo_lopez_graph(d - 2)
                consider(ar[0], ar[1])
            except Exception:
                pass

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: unstructured random biregular graphs repaired by annealing.
    res = _random_search(d, D, deadline, rng)
    if res is not None:
        M, ea, eb = res
        edges = [(int(a), M + int(b)) for a, b in zip(ea, eb)]
        consider(2 * M, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
