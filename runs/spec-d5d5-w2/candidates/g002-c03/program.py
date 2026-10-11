import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured baselines: projective planes (D = 3) and the generalized
# quadrangle W(q) (D = 4). These are the safe starting points.
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
# Bold new construction for the generic case: simulated annealing over
# edge swaps on d-regular bipartite graphs with N vertices per side.
# Edge swaps (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) keep the graph simple,
# d-regular and bipartite. The cost is the number of ordered vertex pairs
# at distance greater than D, counted with bitmask BFS balls.
# ----------------------------------------------------------------------------

def _cost(N, D, adjA, adjB):
    """Number of ordered vertex pairs not within distance D (0 means diameter <= D)."""
    V = 2 * N
    nbr = [None] * V
    for i in range(N):
        nbr[i] = [N + j for j in adjA[i]]
    for j in range(N):
        nbr[N + j] = list(adjB[j])
    reach = [1 << v for v in range(V)]
    for _ in range(D):
        new = [0] * V
        for v in range(V):
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(V - r.bit_count() for r in reach)


def _anneal(N, d, D, deadline, rng):
    """Anneal a d-regular bipartite graph on N + N vertices; return edge list or None."""
    shifts = rng.sample(range(N), d)
    adjA = [set((i + s) % N for s in shifts) for i in range(N)]
    adjB = [set() for _ in range(N)]
    for i in range(N):
        for j in adjA[i]:
            adjB[j].add(i)
    E = [(i, j) for i in range(N) for j in adjA[i]]
    M = len(E)
    cur = _cost(N, D, adjA, adjB)
    T0 = max(2.0, 0.05 * cur)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)

    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * max(0.0, 1.0 - (now - t0) / span) + 0.3
        x = rng.randrange(M)
        y = rng.randrange(M)
        if x == y:
            continue
        a1, b1 = E[x]
        a2, b2 = E[y]
        if a1 == a2 or b1 == b2:
            continue
        if b2 in adjA[a1] or b1 in adjA[a2]:
            continue
        # Apply the swap.
        adjA[a1].discard(b1)
        adjB[b1].discard(a1)
        adjA[a2].discard(b2)
        adjB[b2].discard(a2)
        adjA[a1].add(b2)
        adjB[b2].add(a1)
        adjA[a2].add(b1)
        adjB[b1].add(a2)
        new = _cost(N, D, adjA, adjB)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
            E[x] = (a1, b2)
            E[y] = (a2, b1)
        else:
            # Revert the swap.
            adjA[a1].discard(b2)
            adjB[b2].discard(a1)
            adjA[a2].discard(b1)
            adjB[b1].discard(a2)
            adjA[a1].add(b1)
            adjB[b1].add(a1)
            adjA[a2].add(b2)
            adjB[b2].add(a2)

    if cur == 0:
        return [(i, N + j) for i in range(N) for j in adjA[i]]
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

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: annealed d-regular bipartite graphs, sweeping N upward.
    if D >= 3 and d >= 2 and best[0] < moore:
        N = max(d + 1, int(0.42 * moore / 2))
        while time.monotonic() < deadline and best[0] < moore:
            now = time.monotonic()
            remaining = deadline - now
            slice_end = min(deadline, now + max(2.0, min(12.0, remaining)))
            edges = _anneal(N, d, D, slice_end, rng)
            if edges is not None:
                consider(2 * N, edges)
                N = max(N + 1, best[0] // 2 + 1)
            # On failure, retry the same N with a fresh random start.

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
