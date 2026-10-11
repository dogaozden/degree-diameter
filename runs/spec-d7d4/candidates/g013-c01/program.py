import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: projective planes (D = 3) and generalized quadrangles W(q) (D >= 4).
# Both incidence graphs are bipartite with points on side 0 and lines on side 1.
# ----------------------------------------------------------------------------

def _largest_pp(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
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


# ----------------------------------------------------------------------------
# Spare-degree saturation: add cross-side edges between deficient vertices.
# Adding edges never increases a distance, so diameter validity is kept.
# ----------------------------------------------------------------------------

def _saturate(n, edges, d, color, rng):
    deg = [0] * n
    existing = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        existing.add((min(u, v), max(u, v)))
    L = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    R = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    new = []
    for _ in range(3):
        rng.shuffle(L)
        for a in L:
            if deg[a] >= d:
                continue
            rs = [b for b in R if deg[b] < d]
            rng.shuffle(rs)
            for b in rs:
                if deg[a] >= d:
                    break
                key = (min(a, b), max(a, b))
                if key in existing or deg[b] >= d:
                    continue
                existing.add(key)
                new.append((a, b))
                deg[a] += 1
                deg[b] += 1
    return list(edges) + new


# ----------------------------------------------------------------------------
# New construction: cyclic bi-Haar graphs H(Z_m, S), |S| = d.
# Vertices a_i = i and b_j = m + j; a_i ~ b_{i+s} for s in S.
# The group Z_m acts transitively on each side, so distances are fully
# determined by balls around a_0 and b_0. The cost is the number of
# unreached (source, vertex) pairs within radius D, found by annealing S.
# ----------------------------------------------------------------------------

def _haar_cost(m, S, D):
    N = 2 * m
    total = 0
    for src in (0, m):
        seen = {src}
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < m:
                    nbrs = [m + ((u + s) % m) for s in S]
                else:
                    j = u - m
                    nbrs = [(j - s) % m for s in S]
                for v in nbrs:
                    if v not in seen:
                        seen.add(v)
                        nxt.append(v)
            frontier = nxt
            if not frontier:
                break
        total += N - len(seen)
    return total


def _haar_search(m, d, D, rng, deadline, iters):
    if d > m:
        return None
    S = rng.sample(range(m), d)
    inS = set(S)
    cost = _haar_cost(m, S, D)
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 2.0 * (0.02 ** (it / iters))
        idx = rng.randrange(d)
        old = S[idx]
        new = rng.randrange(m)
        if new in inS:
            continue
        S[idx] = new
        c2 = _haar_cost(m, S, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            inS.discard(old)
            inS.add(new)
            cost = c2
        else:
            S[idx] = old
    if cost == 0:
        return sorted(S)
    return None


def _haar_edges(m, S):
    return [(i, m + (i + s) % m) for i in range(m) for s in S]


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.80 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    # Algebraic bases.
    if D == 3:
        q = _largest_pp(d - 1)
        if q is not None:
            n0, e0 = lib.projective_plane_incidence(q)
            color = [0 if v < n0 // 2 else 1 for v in range(n0)]
            consider(n0, e0)
            consider(n0, _saturate(n0, e0, d, color, rng))
    elif D >= 4:
        q = _largest_pp(min(d - 1, 9))
        if q is not None:
            n0, e0 = _gq_w(q)
            color = [0 if v < n0 // 2 else 1 for v in range(n0)]
            consider(n0, e0)
            consider(n0, _saturate(n0, e0, d, color, rng))

    if best[0] >= moore:
        return best

    # Main search: cyclic bi-Haar graphs, growing m while annealing succeeds.
    m = max(d, best[0] // 2 + 1)
    slice_len = max(2.0, 0.15 * time_limit)
    while time.monotonic() < deadline:
        if 2 * m > moore:
            break
        slice_end = min(deadline, time.monotonic() + slice_len)
        S = _haar_search(m, d, D, rng, slice_end, 40000)
        if S is not None:
            consider(2 * m, _haar_edges(m, S))
            m += 1
        # On failure keep the same m and retry with fresh random starts.

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
