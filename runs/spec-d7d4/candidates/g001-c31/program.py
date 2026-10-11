import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic bases (kept as safe candidates).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bold change: Haar graphs (bi-Cayley over Z_m with one side-swapping shift set)
# searched by annealing on the eccentricity of a single vertex.
#
# Haar graph H(m, S): a_i ~ b_{i+s} for s in S, |S| = d, 0 in S.
# The map a_i -> b_{-i}, b_j -> a_{-j} is an automorphism swapping the sides,
# and translations act transitively on each side, so H is vertex-transitive.
# Hence diameter <= D iff every vertex is within distance D of a_0.
# This makes the cost a single BFS, roughly 2m times cheaper than all-pairs.
# ----------------------------------------------------------------------------

def _haar_cost(m, S, D):
    """Number of vertices at distance > D from a_0 in H(m, S). Zero means diameter <= D."""
    seen = bytearray(2 * m)
    seen[0] = 1
    frontier = [0]
    count = 1
    for _ in range(D):
        nxt = []
        for v in frontier:
            if v < m:
                for s in S:
                    w = m + (v + s) % m
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            else:
                j = v - m
                for s in S:
                    w = (j - s) % m
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
        count += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return 2 * m - count


def _anneal_haar(d, D, m, rng, deadline, iters):
    """Search S (|S| = d, 0 in S) in Z_m so that H(m, S) has diameter <= D."""
    if m < d + 1:
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    c = _haar_cost(m, S, D)
    for it in range(iters):
        if c == 0:
            return S
        if time.monotonic() > deadline:
            break
        T = max(0.05, 1.0 - it / iters)
        i = rng.randrange(1, d)
        cand = rng.randrange(1, m)
        if cand in S:
            continue
        old = S[i]
        S[i] = cand
        c2 = _haar_cost(m, S, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
        else:
            S[i] = old
    return list(S) if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: Haar graphs of increasing order, annealed for diameter D.
    half = max(d + 1, lib._moore_bound(d, D) // 2)   # bipartite Moore bound on m
    m_lo = max(d + 1, int(0.66 * half))
    best_m = best_n // 2

    while time.monotonic() < deadline:
        if best_m >= m_lo and rng.random() < 0.6:
            m = best_m + 1 + rng.randrange(0, 4)
        else:
            m = m_lo + rng.randrange(0, 10)
        m = min(m, half)
        if m <= best_m:
            break
        S = _anneal_haar(d, D, m, rng, deadline, iters=2500)
        if S is not None:
            n, e = lib.haar_graph(m, S)
            if consider(n, e):
                best_m = max(best_m, m)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
