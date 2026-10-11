import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Known families for D = 3, 4: projective plane, Araujo-Pardo-Lopez, and the
# generalized quadrangle W(q).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
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
    """W(q) for the largest prime power q with q + 1 <= d (restricted to small q)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction: vectorized bi-Cayley search over nonabelian groups.
#
# A bi-Cayley graph on one group G with connection set S (|S| = d):
#   A_g is joined to B_{g*s} for every s in S.
# Left translations are automorphisms, so a graph has diameter <= D exactly
# when every vertex is within D of A_e and of B_e. The cost is the number of
# unreached vertices from those two sources, computed with numpy frontier
# expansion on a precomputed multiplication table. Nonabelian groups (small
# semidirect products Z_m x| Z_k with r != 1) make the balls grow much faster
# than cyclic groups, which collide heavily.
# ----------------------------------------------------------------------------

def _moore_half(d, D):
    """Per-side Moore-type size for the search window (heuristic only)."""
    if d <= 2:
        return max(1, D)
    return sum((d - 1) ** i for i in range(D))


def _nonabelian_options(G):
    """All (m, k, r) with G = m*k, r != 1, gcd(r, m) = 1, r^k = 1 mod m."""
    opts = []
    for k2 in range(2, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                opts.append((m, k2, r))
    return opts


def _group_mul(G, rng):
    """Multiplication function of a random group of order G, identity coded as 0."""
    opts = _nonabelian_options(G)
    if opts and rng.random() < 0.9:
        m, k2, r = rng.choice(opts)
        return lib.semidirect_group(m, k2, r)[1]
    return lambda x, y: (x + y) % G


def _group_tables(G, mul):
    """Return (M, inv): M[x, y] = x*y and inv[x] = x^(-1)."""
    M = np.array([[mul(x, y) for y in range(G)] for x in range(G)], dtype=np.int64)
    inv = np.zeros(G, dtype=np.int64)
    rows, cols = np.nonzero(M == 0)  # identity is element 0
    inv[rows] = cols
    return M, inv


def _cost_cayley(M, inv, S, G, D):
    """Unreached (source, vertex) pairs from A_e and B_e within distance D; 0 means valid."""
    Sarr = np.asarray(S, dtype=np.int64)
    Sinv = inv[Sarr]
    total = 0
    for start_side in (0, 1):
        seen = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]  # seen[0] = A, seen[1] = B
        seen[start_side][0] = True
        fr = np.array([0], dtype=np.int64)
        side = start_side
        for _ in range(D):
            gens = Sarr if side == 0 else Sinv
            nb = M[fr][:, gens].ravel()
            nb = nb[~seen[1 - side][nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[1 - side][nb] = True
            fr = nb
            side = 1 - side
        total += 2 * G - int(seen[0].sum()) - int(seen[1].sum())
    return total


def _anneal_cayley(d, D, G, M, inv, rng, deadline, iters):
    """Simulated annealing over connection sets S of size d. Returns (S or None, cost)."""
    S = rng.sample(range(G), d)
    cost = _cost_cayley(M, inv, S, G, D)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.999)
        limit = cost - T * math.log(1.0 - rng.random())
        idx = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        S2 = list(S)
        S2[idx] = new
        c2 = _cost_cayley(M, inv, S2, G, D)
        if c2 <= limit:
            S, cost = S2, c2
    return (S if cost == 0 else None), cost


def _cayley_edges(G, M, S):
    """Edges of the bi-Cayley graph: A_g = g, B_h = G + h, edge A_g -- B_{g*s}."""
    E = []
    for s in S:
        for g in range(G):
            E.append((g, G + int(M[g, s])))
    return 2 * G, E


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 0:
        return 1, []
    if D == 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

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

    # Vectorized bi-Cayley search over nonabelian groups, targeting orders
    # just above the current best. Successes push the window upward.
    if D >= 3:
        half = _moore_half(d, D)
        lo = max(best_n // 2 + 1, int(0.42 * half), 2)
        hi = min(lo + 40, half)
        while lo <= hi and time.monotonic() < deadline:
            G = rng.randint(lo, hi)
            if G < d:
                lo = d
                continue
            mul = _group_mul(G, rng)
            M, inv = _group_tables(G, mul)
            S, _ = _anneal_cayley(d, D, G, M, inv, rng, deadline, 1500)
            if S is not None:
                n, e = _cayley_edges(G, M, S)
                consider(n, e)
                lo = G + 1
                hi = min(lo + 40, half)

    return best_n, best_e
