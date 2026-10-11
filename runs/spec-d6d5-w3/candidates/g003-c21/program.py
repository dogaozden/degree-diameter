import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Cheap baseline families (kept as the safe fallback path).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 9 for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New family: bipartite regular graphs on two sides of size s, found by
# degree-preserving edge switches (double-edge swaps between two A-B edges)
# with simulated annealing on the number of vertex pairs at distance > D.
#
# Vertices: A = 0..s-1, B = s..2s-1. Every vertex has degree exactly d.
# The circulant start (i, i+t mod s), t < d, is simple and bipartite; switches
# randomise it while keeping degrees and simplicity.
# ----------------------------------------------------------------------------

def _bad_pairs(N, adj, D):
    """Ordered count of (source, target) pairs at distance > D, via bitmask balls."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        nxt = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        if nxt == reach:
            break
        reach = nxt
    return sum(N - r.bit_count() for r in reach)


def _switch_search(s, d, D, deadline, rng):
    """Anneal a d-regular bipartite graph on sides of size s. Returns edge list (i, j) or None."""
    el = [(i, (i + t) % s) for i in range(s) for t in range(d)]
    es = {i * s + j for i, j in el}
    N = 2 * s
    m = len(el)

    def adjacency():
        adj = [[] for _ in range(N)]
        for i, j in el:
            adj[i].append(s + j)
            adj[s + j].append(i)
        return adj

    cur = _bad_pairs(N, adjacency(), D)
    t0 = time.monotonic()
    span = max(1e-9, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        T = 0.5 + 6.0 * (1.0 - frac)

        a = rng.randrange(m)
        b = rng.randrange(m)
        if a == b:
            continue
        i1, j1 = el[a]
        i2, j2 = el[b]
        if i1 == i2 or j1 == j2:
            continue
        k1 = i1 * s + j2
        k2 = i2 * s + j1
        if k1 in es or k2 in es:
            continue

        # Apply switch: (i1,j1),(i2,j2) -> (i1,j2),(i2,j1).
        el[a] = (i1, j2)
        el[b] = (i2, j1)
        es.discard(i1 * s + j1)
        es.discard(i2 * s + j2)
        es.add(k1)
        es.add(k2)

        new = _bad_pairs(N, adjacency(), D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            el[a] = (i1, j1)
            el[b] = (i2, j2)
            es.discard(k1)
            es.discard(k2)
            es.add(i1 * s + j1)
            es.add(i2 * s + j2)
    return el


def _switch_ladder(d, D, hard, rng, consider):
    """Binary-search the largest side size s for which the switch annealer succeeds."""
    half = max(d + 2, lib.moore_bound(d, D) // 2)
    lo, hi = 0, max(d + 3, int(half * 0.7))
    s = max(d + 2, int(half * 0.4))
    while time.monotonic() < hard - 0.5 and hi - lo > 2:
        s = min(max(s, lo + 1), hi - 1)
        now = time.monotonic()
        slice_end = min(hard, now + max(2.0, (hard - now) * 0.45))
        el = _switch_search(s, d, D, slice_end, rng)
        if el is not None:
            n = 2 * s
            edges = [(i, s + j) for i, j in el]
            consider(n, edges)
            lo = s
        else:
            hi = s
        s = (lo + hi) // 2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard = start + 0.8 * time_limit
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

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
            ar = _araujo(d)
            if ar is not None:
                consider(ar[0], ar[1])

        if D >= 4:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        # Main new construction for D >= 4 and d >= 3: bipartite regular
        # switch-annealed graphs with a binary search over side size.
        if D >= 4 and d >= 3:
            _switch_ladder(d, D, hard, rng, consider)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
