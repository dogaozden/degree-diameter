import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured baselines: PG(2, q) for D = 3, W(q) for D = 4.
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bold change: repair search over bipartite d-regular graphs.
#
# Start from a simple d-regular bipartite graph on N + N vertices (a Haar-type
# graph with d random shifts), then anneal over double-edge swaps. Swaps keep
# every vertex at degree exactly d and keep the graph simple. The cost is the
# number of unordered vertex pairs at distance more than D, computed with
# big-integer bitset balls. A cost of 0 is a valid diameter-D graph.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs count)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _swap(E, adj, eset, i, j):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Applying it twice restores the graph."""
    a1, b1 = E[i]
    a2, b2 = E[j]
    eset.discard((a1, b1))
    eset.discard((a2, b2))
    eset.add((a1, b2))
    eset.add((a2, b1))
    adj[a1].remove(b1)
    adj[b1].remove(a1)
    adj[a2].remove(b2)
    adj[b2].remove(a2)
    adj[a1].append(b2)
    adj[b2].append(a1)
    adj[a2].append(b1)
    adj[b1].append(a2)
    E[i] = (a1, b2)
    E[j] = (a2, b1)


def _rebuild(n, E):
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    return adj, set(E)


def _anneal(d, D, N, rng, deadline):
    """Anneal double-edge swaps on a d-regular bipartite graph with N vertices per side.

    Returns the edge list [(a, b)] with a in 0..N-1 and b in N..2N-1 if the
    diameter is at most D, else None.
    """
    if N < d:
        return None
    n = 2 * N
    shifts = rng.sample(range(N), d)
    E = [(a, N + (a + s) % N) for a in range(N) for s in shifts]
    adj, eset = _rebuild(n, E)
    cost = _bad(n, adj, D)
    best_cost = cost
    best_E = list(E)
    m = len(E)
    cycle = 2000
    T0_rel, T1_rel = 1.0, 0.02
    it = 0
    while cost > 0 and time.monotonic() < deadline:
        it += 1
        if it % cycle == 0:
            # Restart the cooling cycle from the best state found so far.
            E = list(best_E)
            adj, eset = _rebuild(n, E)
            cost = best_cost
            continue
        f = T0_rel * (T1_rel / T0_rel) ** ((it % cycle) / cycle)
        T = (0.3 + 0.01 * cost) * f
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or (a1, b2) in eset or (a2, b1) in eset:
            continue
        _swap(E, adj, eset, i, j)
        c2 = _bad(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / max(T, 1e-9)):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_E = list(E)
        else:
            _swap(E, adj, eset, i, j)
    if best_cost == 0:
        return list(best_E)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baselines.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    elif D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best[0] >= moore:
        return best

    # Repair search ladder over the half-order N (total order 2N).
    # The d=5, D=5 target starts at N = 170, just above the record N = 168.
    hint = 170 if (d, D) == (5, 5) else None
    N = hint if hint is not None else best[0] // 2 + 1

    while time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if N < lo:
            N = lo
        if 2 * N > moore:
            break
        now = time.monotonic()
        slice_end = now + 0.45 * (deadline - now)
        E = _anneal(d, D, N, rng, slice_end)
        if E is not None:
            consider(2 * N, E)
            N = best[0] // 2 + 1
        else:
            N -= 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
