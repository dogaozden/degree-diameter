"""Lift-based construction for diameter-5 targets, with a safe fallback.

Idea: for d - 1 = q a prime power (q <= 9), the generalized quadrangle W(q) incidence
graph is d-regular, bipartite, of order 2(q+1)(q^2+1) and has diameter 4. Its voltage
lifts over Z_m are still d-regular and bipartite, with order m times the base order.
Diameter 5 is a much weaker requirement than the base's diameter 4 plus slack, so
simulated annealing over edge voltages can often find lifts of diameter <= 5 at
orders the parent never reached (for d=9, the m=2 lift has 2340 vertices, above the
parent's 2304).

Coverage check: a lift over an abelian group acts by translations on fibres, so the
distance from (x,g) to (y,h) equals the distance from (x,0) to (y,h-g). It is enough
to check, for every base source x, that every lifted vertex is within D steps. This is
done with packed uint64 bitsets over the base sources. Every result passes lib.is_valid
before it is kept. The fallback is K_{d,d}, the parent's constructions, and the
best valid graph found so far.

Honest expectation: beating the record (2496) may not happen within 60 s of Python
annealing. The lift stage is conservative in what it keeps: it only replaces the
incumbent when a larger graph validates.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


_POP16 = np.array([bin(i).count("1") for i in range(1 << 16)], dtype=np.int64)


def _popcount(B):
    """Total number of set bits in a C-contiguous uint64 array."""
    return int(_POP16[B.view(np.uint16)].sum())


# ----------------------------------------------------------------------------
# Base constructions (exact, used as the safe incumbent).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, (q+1)-regular."""
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


# ----------------------------------------------------------------------------
# Regular voltage lifts over Z_m.
# ----------------------------------------------------------------------------

def _regular_slots(nbc, edges, dd):
    """Return (nb, rev): nb[u, l] is the l-th neighbour of u, rev[u, l] is u's slot at that neighbour.

    Returns None if the base graph is not dd-regular.
    """
    adj = [[] for _ in range(nbc)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != dd for a in adj):
        return None
    where = {}
    for v in range(nbc):
        for k, u in enumerate(adj[v]):
            where[(v, u)] = k
    nb = np.array(adj, dtype=np.int64)
    rev = np.zeros((nbc, dd), dtype=np.int64)
    for u in range(nbc):
        for l, v in enumerate(adj[u]):
            rev[u, l] = where[(v, u)]
    return nb, rev


def _lift_nbr(nb, vol, m):
    """Neighbour table of the Z_m lift: lifted vertex u*m+g has slot-l neighbour nb[u,l]*m + (g+vol[u,l]) % m."""
    nbc, dd = nb.shape
    g = np.arange(m, dtype=np.int64)
    nbr = np.empty((dd, nbc * m), dtype=np.int64)
    for l in range(dd):
        nbr[l] = (nb[:, l, None] * m + (g[None, :] + vol[:, l, None]) % m).reshape(-1)
    return nbr


def _cover_cost(nbr, nbc, m, D):
    """Number of (base source x, lifted vertex t) pairs at distance > D from source (x, 0).

    Zero means the lift has diameter <= D. Bit x of B[t] says source x reaches t within
    the current number of steps.
    """
    N = nbc * m
    W = (nbc + 63) // 64
    B = np.zeros((N, W), dtype=np.uint64)
    x = np.arange(nbc, dtype=np.int64)
    B[x * m, x // 64] = np.uint64(1) << (x % 64).astype(np.uint64)
    for _ in range(D):
        new = B.copy()
        for l in range(nbr.shape[0]):
            new |= B[nbr[l]]
        B = new
    return N * nbc - _popcount(B)


def _lift_edges(nb, vol, m):
    """Edge list (n, edges) of the lift defined by vol."""
    nbr = _lift_nbr(nb, vol, m)
    N = nbr.shape[1]
    edges = set()
    for l in range(nbr.shape[0]):
        for x, y in enumerate(nbr[l].tolist()):
            edges.add((x, y) if x < y else (y, x))
    return N, sorted(edges)


def _lift_search(nb, rev, eu, el, m, D, rng, deadline):
    """Simulated annealing over edge voltages. Returns (n, edges) of a diameter-D lift, or None."""
    nbc, dd = nb.shape
    vol = np.zeros((nbc, dd), dtype=np.int64)
    for u, l in zip(eu, el):
        v = int(nb[u, l])
        k = int(rev[u, l])
        a = rng.randrange(m)
        vol[u, l] = a
        vol[v, k] = (-a) % m

    cur = _cover_cost(_lift_nbr(nb, vol, m), nbc, m, D)
    c0 = float(max(cur, 1))
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    E = len(eu)
    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        temp = max(0.5, 0.01 * c0 * (1.0 - frac))
        i = rng.randrange(E)
        u, l = eu[i], el[i]
        v, k = int(nb[u, l]), int(rev[u, l])
        old = int(vol[u, l])
        new = rng.randrange(m)
        if new == old:
            continue
        vol[u, l] = new
        vol[v, k] = (-new) % m
        c2 = _cover_cost(_lift_nbr(nb, vol, m), nbc, m, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
        else:
            vol[u, l] = old
            vol[v, k] = (-old) % m
    if cur != 0:
        return None
    return _lift_edges(nb, vol, m)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard_end = start + max(1.0, min(time_limit - 6.0, 0.9 * time_limit))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact D = 3 construction (calibration case d = 3).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Base for D >= 4: W(q) with q = d-1, which is d-regular and has diameter 4.
    base = None
    if D >= 4 and 2 <= d - 1 <= 9 and lib.is_prime_power(d - 1) and time.monotonic() < hard_end:
        base = _gq_w(d - 1)
        consider(base[0], base[1])
        if D == 4:
            return best

    # New family for D >= 5: regular Z_m lifts of the base, searched by annealing.
    if D >= 5 and base is not None and time.monotonic() < hard_end:
        nbc = base[0]
        slots = _regular_slots(nbc, base[1], d)
        if slots is not None:
            nb, rev = slots
            eu, el = [], []
            for u in range(nbc):
                for l in range(d):
                    if u < int(nb[u, l]):
                        eu.append(u)
                        el.append(l)
            m0 = max(2, best[0] // nbc + 1)
            m = m0
            while m <= 8 and time.monotonic() < hard_end - 1.0:
                now = time.monotonic()
                left = hard_end - now
                # The first, smaller lift gets a bounded share; later attempts use the rest.
                dl = now + (0.6 * left if m == m0 else left)
                res = _lift_search(nb, rev, eu, el, m, D, rng, dl)
                if res is None:
                    break
                consider(res[0], res[1])
                m = max(m + 1, best[0] // nbc + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
