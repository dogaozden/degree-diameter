import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / structured baselines (kept as safe fallbacks).
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
# New main construction: bi-Cayley graphs (Haar-type) over finite groups
# G = Z_m x| Z_k2, with one vertex per side per group element.
#
# Vertices: A_g = g (0..G-1), B_h = G + h.
# Connection set S of d distinct group elements: A_g ~ B_{g*s} for s in S.
# Left multiplication is an automorphism that is transitive on each side,
# so the graph has diameter <= D iff every vertex is within D of A_1 and of B_1.
#
# Search: simulated annealing over the connection set S for many groups of
# order just above the current best, keeping the largest valid graph found.
# The annealing cost is the number of unreached (source, vertex) pairs,
# evaluated with numpy boolean reachability from the two sources.
# ----------------------------------------------------------------------------

def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h. r = 1 gives the direct product.
    """
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _sample_group_of_order(G, rng):
    """Return (m, k2, r) with m*k2 == G, m >= 2 (or G prime-cyclic), r valid for Z_m x| Z_k2."""
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    for _ in range(40):
        k2 = rng.choice(divs)
        m = G // k2
        if k2 == 1:
            return m, 1, 1
        r = 1
        for _ in range(60):
            c = rng.randrange(1, m) if m > 1 else 1
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
        return m, k2, r
    return None


def _set_layer(nbrs, G, Ts, Invs, S, l):
    s = S[l]
    nbrs[l, :G] = G + Ts[s]
    nbrs[l, G:] = Invs[s]


def _cost(nbrs, d, G, D):
    """Number of unreached (source, vertex) pairs for sources A_1 and B_1 within distance D."""
    N = 2 * G
    reach = np.zeros((2, N), dtype=bool)
    reach[0, 0] = True
    reach[1, G] = True
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[:, nbrs[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return 2 * N - int(reach.sum())


def _anneal(d, D, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over the connection set. Returns S (list of d elements) or None."""
    if G < d + 1:
        return None
    S = rng.sample(range(G), d)
    nbrs = np.empty((d, 2 * G), dtype=np.int64)
    for l in range(d):
        _set_layer(nbrs, G, Ts, Invs, S, l)
    c = _cost(nbrs, d, G, D)
    c0 = float(max(c, 1))
    for t in range(iters):
        if c == 0:
            break
        if (t & 31) == 0 and time.monotonic() > deadline:
            break
        temp = max(0.5, 0.05 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[l]
        S[l] = new
        _set_layer(nbrs, G, Ts, Invs, S, l)
        c2 = _cost(nbrs, d, G, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            c = c2
        else:
            S[l] = old
            _set_layer(nbrs, G, Ts, Invs, S, l)
    if c != 0:
        return None
    return S


def _edges_from_set(S, G, Ts):
    edges = []
    for s in S:
        row = Ts[s].tolist()
        for u in range(G):
            edges.append((u, G + row[u]))
    return edges


# ----------------------------------------------------------------------------
# Top level.
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

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

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

    moore = lib._moore_bound(d, D)
    if best_n >= moore:
        return best

    # Main search: bi-Cayley graphs over groups of order just above the best half-order.
    best_G = best_n // 2
    window = 6
    while time.monotonic() < deadline:
        G = best_G + 1 + rng.randrange(window)
        if 2 * G > moore:
            G = max(d + 1, moore // 2)
            if 2 * G <= best_n:
                break
        g = _sample_group_of_order(G, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        S = _anneal(d, D, G, Ts, Invs, rng, deadline, 3000)
        if S is None:
            continue
        n = 2 * G
        if n > best_n:
            e = _edges_from_set(S, G, Ts)
            if lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
                best_G = G

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
