import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe exact baselines.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction: Haar-type Cayley bipartite graphs over non-abelian groups.
#
# Group G = Z_m x| Z_k (element a*k+b, (a,b)(c,e) = (a + r^b c, b+e)).
# Vertices a_g (index g) and b_h (index G+h). With connection set S, |S| = d,
# a_g ~ b_{g s} for s in S. This is d-regular and bipartite.
#
# Left multiplication is an automorphism, so the distance structure is covered
# by BFS from a_e and b_e only. Cost = number of unreached (source, vertex)
# pairs, and cost 0 means diameter <= D. Search: simulated annealing over S.
# A ratchet over the group order G keeps raising the target as successes come.
# ----------------------------------------------------------------------------

def _group_tables(m, k, r):
    """Return (G, Ts, Invs): Ts[s, g] = g*s and Invs[s, h] = g with g*s = h."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + pw[b[:, None]] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _nbrs(G, Ts, Invs, S):
    """Neighbour table of shape (d, 2G) for connection set S."""
    d = len(S)
    nbr = np.empty((d, 2 * G), dtype=np.int64)
    for j, s in enumerate(S):
        nbr[j, :G] = G + Ts[s]
        nbr[j, G:] = Invs[s]
    return nbr


def _unreached(G, nbr, D):
    """Number of (source, vertex) pairs at distance > D, for sources a_e and b_e."""
    N = 2 * G
    R = np.zeros((2, N), dtype=bool)
    R[0, 0] = True
    R[1, G] = True
    for _ in range(D):
        new = R.copy()
        for row in nbr:
            new |= R[:, row]
        if np.array_equal(new, R):
            break
        R = new
    return int(R.size - int(R.sum()))


def _anneal(G, Ts, Invs, d, D, rng, deadline, iters):
    """Search a connection set S of size d with diameter <= D. Returns S or None."""
    S = rng.sample(range(G), d)
    cost = _unreached(G, _nbrs(G, Ts, Invs, S), D)
    c0 = float(max(cost, 1))
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        j = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[j]
        S[j] = new
        c2 = _unreached(G, _nbrs(G, Ts, Invs, S), D)
        temp = max(0.5, 0.02 * c0 * (1.0 - t / iters))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[j] = old
    return S if cost == 0 else None


def _pick_group(G, rng):
    """Return (m, k, r) with m*k = G, using a random divisor k and a random automorphism r when possible."""
    ks = [k for k in range(1, 41) if G % k == 0 and G // k >= 3]
    if not ks:
        return G, 1, 1
    k = rng.choice(ks)
    m = G // k
    if k == 1:
        return m, 1, 1
    for _ in range(200):
        r = rng.randrange(2, m)
        if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
            return m, k, r
    return m, k, 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, time_limit - 6.0)
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
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
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

    # Haar-type Cayley search with a ratchet on the group order.
    moore = lib.moore_bound(d, D)
    hi_fixed = max(20, int(0.25 * moore))
    while time.monotonic() < deadline:
        lo = max(d, best_n // 2 + 1)
        hi = max(hi_fixed, lo + 10)
        G = lo + int((hi - lo) * rng.random() ** 2)
        if G < d:
            continue
        m, k, r = _pick_group(G, rng)
        G, Ts, Invs = _group_tables(m, k, r)
        S = _anneal(G, Ts, Invs, d, D, rng, deadline, 2500)
        if S is None:
            continue
        edges = [(g, G + int(v)) for s in S for g, v in enumerate(Ts[s].tolist())]
        consider(2 * G, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
