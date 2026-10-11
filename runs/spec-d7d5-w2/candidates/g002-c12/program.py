import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact constructions (kept as they are; they return immediately when optimal).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph of degree d (q = d - 2 a prime power >= 3); diameter 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    return lib.araujo_lopez_graph(q)


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
# New construction: simulated annealing over simple d-regular bipartite graphs.
#
# Parts A = 0..N-1 and B = N..2N-1; every edge joins A to B, so the graph is
# bipartite by construction. Each A vertex has exactly d edge slots (edge a*d+k).
# The B-side assignment eb[e] is a multiset in which every B vertex appears d
# times. A move swaps the B endpoints of two edges. Simple-ness is kept by a
# set of present (a, b) keys. Cost = number of ordered pairs at distance > D,
# computed with packed uint64 bitsets (one bit per vertex) and D rounds of
# neighbourhood OR-propagation.
# ----------------------------------------------------------------------------

_POP16 = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _nbr_arrays(N, d, ea, eb_list):
    """Return the (2N, d) neighbour table for the current edge assignment."""
    eb = np.array(eb_list, dtype=np.int64)
    nbrA = (N + eb).reshape(N, d)
    order = np.argsort(eb, kind="stable")
    nbrB = ea[order].reshape(N, d)
    return np.vstack([nbrA, nbrB])


def _bad_pairs(V, D, nbr):
    """Number of ordered vertex pairs (u, v) with dist(u, v) > D."""
    W = (V + 63) // 64
    reach = np.zeros((V, W), dtype=np.uint64)
    idx = np.arange(V, dtype=np.int64)
    reach[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(D):
        gathered = reach[nbr]
        new = reach | np.bitwise_or.reduce(gathered, axis=1)
        if np.array_equal(new, reach):
            break
        reach = new
    total = int(_POP16[reach.view(np.uint16)].sum())
    return V * V - total


def _anneal(N, d, D, rng, deadline):
    """Search for a simple d-regular bipartite graph on 2N vertices with diameter <= D.

    Returns (2N, edges) on success, None otherwise.
    """
    if N < d or d < 1:
        return None
    V = 2 * N
    M = N * d
    ea_np = np.repeat(np.arange(N, dtype=np.int64), d)
    ea_l = ea_np.tolist()

    # Start from a circulant with distinct shifts: simple and d-regular.
    shifts = rng.sample(range(N), d)
    eb_l = [(a + s) % N for a in range(N) for s in shifts]
    present = set(ea_l[e] * N + eb_l[e] for e in range(M))

    cost = _bad_pairs(V, D, _nbr_arrays(N, d, ea_np, eb_l))
    start = time.monotonic()
    span = max(1e-6, deadline - start)

    while cost > 0:
        now = time.monotonic()
        if now > deadline:
            return None
        frac = (now - start) / span
        temp = max(0.3, 2.5 * (1.0 - frac))

        e1 = rng.randrange(M)
        e2 = rng.randrange(M)
        a1, b1 = ea_l[e1], eb_l[e1]
        a2, b2 = ea_l[e2], eb_l[e2]
        if a1 == a2 or b1 == b2:
            continue
        k1 = a1 * N + b2
        k2 = a2 * N + b1
        if k1 in present or k2 in present:
            continue

        # Apply the swap.
        eb_l[e1], eb_l[e2] = b2, b1
        present.discard(a1 * N + b1)
        present.discard(a2 * N + b2)
        present.add(k1)
        present.add(k2)

        c2 = _bad_pairs(V, D, _nbr_arrays(N, d, ea_np, eb_l))
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = c2
        else:
            # Revert.
            eb_l[e1], eb_l[e2] = b1, b2
            present.discard(k1)
            present.discard(k2)
            present.add(a1 * N + b1)
            present.add(a2 * N + b2)

    edges = [(ea_l[e], N + eb_l[e]) for e in range(M)]
    return V, edges


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
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    # Exact constructions: return immediately when they are optimal.
    if D >= 3:
        try:
            pg = _best_pg(d)
        except Exception:
            pg = None
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

        if D == 3:
            try:
                aj = _araujo(d)
            except Exception:
                aj = None
            if aj is not None:
                consider(aj[0], aj[1])
                return best

    if D >= 4 and time.monotonic() < deadline:
        try:
            gq = _best_gq(d)
        except Exception:
            gq = None
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if D == 2 or d <= 2:
        return best

    # Bold path: binary search on the half-order N (total order 2N) using annealing.
    lo = max(d, best_n // 2)           # known feasible (N, total order 2N)
    hi = max(lo + 1, lib.moore_bound(d, D) // 2)   # upper limit on N
    while hi - lo > 1 and time.monotonic() < deadline - 1.0:
        remaining = deadline - time.monotonic()
        attempt = min(remaining, max(4.0, 0.25 * budget))
        if attempt <= 0.5:
            break
        mid = (lo + hi) // 2
        if mid <= lo:
            break
        attempt_deadline = time.monotonic() + attempt
        try:
            res = _anneal(mid, d, D, rng, min(attempt_deadline, deadline))
        except Exception:
            res = None
        if res is not None:
            consider(res[0], res[1])
            lo = mid
        else:
            hi = mid

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
