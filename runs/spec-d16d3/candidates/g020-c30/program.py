import math
import random
import time

import lib

# Intersection reduction (used here for D = 3):
# A bipartite graph has diameter <= 3 iff any two vertices on the same side share a
# neighbour. For a non-adjacent pair (a, b), pick any neighbour Y of b; Y shares a
# neighbour X with a, which gives the path a-X-Y-b. So the search only needs two
# families of rows (A-side and B-side neighbourhoods) that are pairwise intersecting,
# with every row size and every column count at most d. Intersection tests are
# bitmask ANDs, so local search can be run directly on the incidence structure.


def _bits(x):
    """Indices of the set bits of a non-negative integer."""
    out = []
    while x:
        low = x & -x
        out.append(low.bit_length() - 1)
        x ^= low
    return out


def _side_cost(rows, S):
    """Number of disjoint pairs that involve at least one row index in S."""
    S = list(S)
    tot = 0
    for x in S:
        rx = rows[x]
        for y in range(len(rows)):
            if y != x and not (rows[y] & rx):
                tot += 1
    inner = 0
    for i in range(len(S)):
        ri = rows[S[i]]
        for j in range(i + 1, len(S)):
            if not (ri & rows[S[j]]):
                inner += 1
    return tot - inner


def _flip(rowA, rowB, degA, degB, flips):
    """Toggle the edges (a, b) in flips. Applying the same flips again reverts them."""
    for a, b in flips:
        rowA[a] ^= 1 << b
        rowB[b] ^= 1 << a
        if (rowA[a] >> b) & 1:
            degA[a] += 1
            degB[b] += 1
        else:
            degA[a] -= 1
            degB[b] -= 1


def _seed(rowX, rowY, x_new, d):
    """Greedily give the empty row x_new neighbours in rowY so that it meets every other row of rowX."""
    unc = ((1 << len(rowX)) - 1) & ~(1 << x_new)
    cnt = 0
    while unc and cnt < d:
        best, bg = -1, 0
        for y in range(len(rowY)):
            if rowY[y].bit_count() >= d or (rowY[y] >> x_new) & 1:
                continue
            g = (rowY[y] & unc).bit_count()
            if g > bg:
                best, bg = y, g
        if best < 0:
            break
        rowX[x_new] |= 1 << best
        rowY[best] |= 1 << x_new
        unc &= ~rowY[best]
        cnt += 1


def _anneal(rowA, rowB, d, rng, deadline):
    """Simulated annealing on edge toggles and swaps. Cost = disjoint same-side pairs.

    Returns (rowA, rowB) with zero cost, or None when the deadline passes first.
    """
    nA, nB = len(rowA), len(rowB)
    degA = [r.bit_count() for r in rowA]
    degB = [r.bit_count() for r in rowB]
    cost = _side_cost(rowA, range(nA)) + _side_cost(rowB, range(nB))
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 2.0, 0.05
    T = T0
    it = 0
    while cost > 0:
        it += 1
        if (it & 127) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        # Bias toward the newest vertices, which carry most of the conflicts.
        a = nA - 1 if rng.random() < 0.3 else rng.randrange(nA)
        b = nB - 1 if rng.random() < 0.3 else rng.randrange(nB)
        if (rowA[a] >> b) & 1:
            if rng.random() < 0.5:
                flips = [(a, b)]
            else:
                b2 = rng.randrange(nB)
                if b2 == b or (rowA[a] >> b2) & 1 or degB[b2] >= d:
                    continue
                flips = [(a, b), (a, b2)]
        else:
            if degB[b] >= d:
                continue
            if degA[a] < d:
                flips = [(a, b)]
            else:
                nb = _bits(rowA[a])
                flips = [(a, rng.choice(nb)), (a, b)]
        Bs = list({bb for _, bb in flips})
        before = _side_cost(rowA, [a]) + _side_cost(rowB, Bs)
        _flip(rowA, rowB, degA, degB, flips)
        after = _side_cost(rowA, [a]) + _side_cost(rowB, Bs)
        delta = after - before
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost += delta
        else:
            _flip(rowA, rowB, degA, degB, flips)
    if cost == 0:
        return rowA, rowB
    return None


def _to_graph(rowA, rowB):
    """Convert row bitmasks to (n, edges): A vertices 0..nA-1, B vertices nA..nA+nB-1."""
    nA = len(rowA)
    edges = [(a, nA + b) for a in range(nA) for b in _bits(rowA[a])]
    return nA + len(rowB), edges


def _pg_rows(q, arc):
    """Row bitmasks of PG(2, q) incidence, plus for each point P in arc a new A-vertex
    on the lines through P and a new B-vertex on the points of line P."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    rowA = [0] * m
    rowB = [0] * m
    for u, v in edges:
        rowA[u] |= 1 << (v - m)
        rowB[v - m] |= 1 << u
    full = (1 << m) - 1
    for P in arc:
        lines = rowA[P] & full
        pts = rowB[P] & full
        xa = len(rowA)
        bb = len(rowB)
        rowA.append(lines)
        rowB.append(pts)
        for L in _bits(lines):
            rowB[L] |= 1 << xa
        for Q in _bits(pts):
            rowA[Q] |= 1 << bb
    return rowA, rowB


def _conic(q):
    """Conic (plus nucleus for even q): an arc, so every line holds at most 2 of its points."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _build_base(d):
    """Best PG(2, q)-based base rows for D = 3, with q the largest prime power below d."""
    qs = [x for x in range(2, d) if lib.is_prime_power(x)]
    if not qs:
        return None
    q = max(qs)
    best = _pg_rows(q, [])
    if d - q - 1 >= 2:
        rA, rB = _pg_rows(q, _conic(q))
        n1, e1 = _to_graph(rA, rB)
        if lib.is_valid(n1, e1, d, 3):
            best = (rA, rB)
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(1.0, min(0.85 * time_limit, time_limit - 5.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    base = _build_base(d)
    if base is None:
        return best_n, best_e
    rowA, rowB = base
    n, e = _to_graph(rowA, rowB)
    if n > best_n and lib.is_valid(n, e, d, D):
        best_n, best_e = n, e
    if D > 3:
        return best_n, best_e

    # Extension search (D = 3): add one A-vertex and one B-vertex, seed them greedily,
    # then anneal until all same-side pairs intersect again.
    rng = random.Random(seed * 1000003 + d * 97 + D)
    if not any(r.bit_count() < d for r in rowA) or not any(r.bit_count() < d for r in rowB):
        return best_n, best_e

    cur = (rowA, rowB)
    while deadline - time.monotonic() > 1.0:
        now = time.monotonic()
        budget = min(deadline - now, 12.0)
        rA = list(cur[0])
        rB = list(cur[1])
        rA.append(0)
        rB.append(0)
        _seed(rA, rB, len(rA) - 1, d)
        _seed(rB, rA, len(rB) - 1, d)
        sol = _anneal(rA, rB, d, rng, now + budget)
        if sol is None:
            continue
        cur = sol
        n, e = _to_graph(*cur)
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    return best_n, best_e
