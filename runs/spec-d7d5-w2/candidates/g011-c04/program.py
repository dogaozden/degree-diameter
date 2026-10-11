import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe exact / baseline families (kept from the parent as fallbacks).
# ----------------------------------------------------------------------------

_POP16 = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


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
# New family: unstructured d-regular bipartite graphs found by simulated
# annealing over edge switches. Each switch keeps bipartiteness and degrees,
# and the cost is the number of ordered vertex pairs at distance > D,
# computed with packed bitsets in numpy.
# ----------------------------------------------------------------------------

def _nbr_from(ea, eb, nA, d):
    """Neighbour table (n, d) for a d-regular bipartite graph given by edge arrays (A ids < nA, B ids >= nA)."""
    n = 2 * nA
    nbr = np.empty((n, d), dtype=np.int64)
    oa = np.argsort(ea, kind="stable")
    nbr[:nA] = eb[oa].reshape(nA, d)
    ob = np.argsort(eb, kind="stable")
    nbr[nA:] = ea[ob].reshape(nA, d)
    return nbr


def _eval(nbr, n, W, D, d):
    """Return (cost, badv): cost = ordered pairs at distance > D; badv[v] = count of vertices unreached from v."""
    reach = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n, dtype=np.int64)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for j in range(d):
            new |= reach[nbr[:, j]]
        if np.array_equal(new, reach):
            break
        reach = new
    rowpop = _POP16[reach.view(np.uint16)].sum(axis=1)
    badv = n - rowpop
    return int(badv.sum()), badv


def _anneal(nA, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph with 2*nA vertices and diameter <= D. Returns (n, edges) or None."""
    n = 2 * nA
    W = (n + 63) // 64
    shifts = np.array(rng.sample(range(nA), d), dtype=np.int64)
    grid = np.arange(nA, dtype=np.int64)[:, None]
    ea = np.repeat(np.arange(nA, dtype=np.int64), d)
    eb = (nA + (grid + shifts[None, :]) % nA).ravel()
    E = int(ea.size)
    keys = set((ea * n + eb).tolist())
    nbr = _nbr_from(ea, eb, nA, d)
    cost, badv = _eval(nbr, n, W, D, d)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)

    while cost > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        T = 3.0 * (1.0 - frac) + 0.2
        i = None
        if rng.random() < 0.5:
            cand = np.flatnonzero((badv[ea] > 0) | (badv[eb] > 0))
            if cand.size:
                i = int(cand[rng.randrange(cand.size)])
        if i is None:
            i = rng.randrange(E)
        j = rng.randrange(E)
        a1, b1 = int(ea[i]), int(eb[i])
        a2, b2 = int(ea[j]), int(eb[j])
        if a1 == a2 or b1 == b2:
            continue
        k1 = a1 * n + b2
        k2 = a2 * n + b1
        if k1 in keys or k2 in keys:
            continue
        eb[i] = b2
        eb[j] = b1
        nbr_new = _nbr_from(ea, eb, nA, d)
        c2, badv2 = _eval(nbr_new, n, W, D, d)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            keys.discard(a1 * n + b1)
            keys.discard(a2 * n + b2)
            keys.add(k1)
            keys.add(k2)
            cost, badv = c2, badv2
        else:
            eb[i] = b1
            eb[j] = b2

    if cost != 0:
        return None
    return n, [(int(a), int(b)) for a, b in zip(ea.tolist(), eb.tolist())]


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (calibration-style early returns, as in the parent).
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

    # Bold new family: annealed unstructured d-regular bipartite graphs.
    # Binary-search-like ladder over the side size nA, with a feasible lower
    # end (current best) and a heuristic upper end (half the Moore bound).
    if d >= 2 and D >= 3:
        moore_half = max(d, lib.moore_bound(d, D) // 2)
        lo = max(d, best_n // 2)
        hi = moore_half
        nA = min(hi, max(lo + 1, int(0.35 * moore_half)))
        while time.monotonic() < deadline - 1.0 and hi > lo:
            now = time.monotonic()
            remaining = deadline - now
            nA = min(max(nA, lo + 1), hi)
            slice_s = max(1.5, remaining * 0.4)
            res = _anneal(nA, d, D, rng, min(deadline, now + slice_s))
            if res is not None:
                consider(res[0], res[1])
                lo = nA
            else:
                hi = nA - 1
            nA = (lo + hi + 1) // 2
            if nA <= lo:
                nA = lo + 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
