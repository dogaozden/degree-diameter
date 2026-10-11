import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (exact constructions and small fallbacks).
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
# New family for the high-order search: bi-Cayley graphs (k = 1) over
# semidirect products G = Z_m x| Z_k2.
#
# Vertices A_g = g and B_h = G + h. Each connection element s in S (|S| = d,
# distinct) gives edges A_g ~ B_{g*s}. Left multiplication by the group is an
# automorphism, so the diameter is decided by two BFS balls: from A_identity
# and from B_identity. Search is simulated annealing over the set S, with a
# bitmask reach cost (0 means diameter <= D).
# ----------------------------------------------------------------------------

_K2 = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 28, 30, 36, 40, 42)


def _all_r(m, k2):
    """All actions r for Z_m x| Z_k2 (r^k2 = 1 mod m, gcd(r, m) = 1)."""
    if m < 2:
        return []
    if k2 == 1:
        return [1]
    out = [1]
    for c in range(2, m):
        if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
            out.append(c)
    return out


def _group_for_order(G, rng):
    """Random (m, k2, r) with m * k2 = G, or None."""
    opts = []
    for k2 in _K2:
        if G % k2 == 0 and G // k2 >= 2:
            m = G // k2
            for r in _all_r(m, k2):
                opts.append((m, k2, r))
    if not opts:
        return None
    return rng.choice(opts)


def _tables(m, k2, r):
    """Return (G, Ts, Invs): Ts[s, g] = g*s and Invs[s, h] = g with g*s = h."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    # M[g, s] = g * s, with (a, b)(c, e) = (a + r^b c, b + e).
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    Invs[np.arange(G)[:, None], Ts] = x[None, :]
    return G, Ts, Invs


def _make_nbr(G, Ts, Invs, S):
    """Neighbour table (d, 2G): row l gives each vertex's neighbour through connection S[l]."""
    d = len(S)
    nbr = np.empty((d, 2 * G), dtype=np.int64)
    for l, s in enumerate(S):
        nbr[l, :G] = G + Ts[s]
        nbr[l, G:] = Invs[s]
    return nbr


def _cost(G, D, nbr):
    """Number of unreached (representative, vertex) pairs; 0 means diameter <= D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    reach[0] = 1          # representative A_identity, bit 0
    reach[G] = 2          # representative B_identity, bit 1
    for _ in range(D):
        new = reach | np.bitwise_or.reduce(reach[nbr], axis=0)
        if np.array_equal(new, reach):
            break
        reach = new
    full = int(np.sum(reach & 1)) + int(np.sum((reach >> 1) & 1))
    return 2 * N - full


def _anneal(d, D, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over the connection set S. Returns S or None."""
    S = rng.sample(range(G), d)
    nbr = _make_nbr(G, Ts, Invs, S)
    cost = _cost(G, D, nbr)
    if cost == 0:
        return S
    T0, T1 = 4.0, 0.5
    for t in range(iters):
        if (t & 255) == 0 and time.monotonic() > deadline:
            break
        temp = T0 * (T1 / T0) ** (t / iters)
        l = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[l]
        S[l] = new
        nbr[l, :G] = G + Ts[new]
        nbr[l, G:] = Invs[new]
        c2 = _cost(G, D, nbr)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            if cost == 0:
                return S
        else:
            S[l] = old
            nbr[l, :G] = G + Ts[old]
            nbr[l, G:] = Invs[old]
    return None


def _edges(G, Ts, S):
    """Edge list of the bi-Cayley graph: A_g ~ B_{g*s} for s in S."""
    edges = []
    for s in S:
        col = Ts[s]
        for g in range(G):
            edges.append((g, G + int(col[g])))
    return 2 * G, edges


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
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

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley search over semidirect products, with adaptive growth of the order.
    if d >= 2:
        moore = lib._moore_bound(d, D)
        half = max(1, moore // 2)
        cur = max(1, best_n // 2)   # a bi-Cayley graph of order 2*cur is assumed achievable
        step = max(4, half // 40)

        while time.monotonic() < deadline:
            G = cur + step
            found = None
            for _ in range(3):
                if time.monotonic() > deadline:
                    break
                grp = _group_for_order(G, rng)
                if grp is None:
                    break
                m, k2, r = grp
                Gc, Ts, Invs = _tables(m, k2, r)
                S = _anneal(d, D, Gc, Ts, Invs, rng, deadline, 6000)
                if S is not None:
                    found = (Gc, Ts, S)
                    break
            if found is None:
                step = max(1, step // 2)
                continue
            Gc, Ts, S = found
            n, e = _edges(Gc, Ts, S)
            consider(n, e)
            cur = Gc

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
