import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe exact baselines (returned immediately where they are known to be optimal).
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
# New construction: Haar graphs (bi-Cayley graphs with one orbit per side)
# over many non-abelian groups Z_m x|_r Z_k.
#
# Vertices: a_g = g (g in G) and b_h = G + h.
# Edges: a_g ~ b_{g*s} for s in S, |S| = d, S a set of distinct group elements.
# Left multiplication is an automorphism that is transitive on each side, so
# diameter <= D is checked by two BFS runs, from a_e and from b_e.
# Search: simulated annealing over S, for group orders N just above the best
# order found so far. Degree is exactly d and the graph is bipartite by design.
# ----------------------------------------------------------------------------

def _sample_group(N, rng):
    """Return (m, k, r) with Z_m x|_r Z_k of order N = m*k."""
    cands = [k for k in range(2, N + 1) if N % k == 0 and N // k >= 2]
    if not cands or rng.random() < 0.05:
        k = 1
    else:
        k = rng.choice(cands)
    m = N // k
    r = 1 % m
    if k > 1 and m > 2:
        for _ in range(80):
            c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
                r = c
                break
    return m, k, r


def _group_tables(m, k, r):
    """Return (G, M, inv) with M[x, y] = x*y and inv[x] = x^{-1}; element a*k+b, (a,b)(c,e)=(a+r^b c, b+e)."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    powers = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    inv = np.empty(G, dtype=np.int64)
    rows, cols = np.nonzero(M == 0)
    inv[rows] = cols
    return G, M, inv


def _unreached(adj, src, D, N2):
    """Number of vertices not within distance D of src in the graph given by adjacency array adj."""
    visited = np.zeros(N2, dtype=bool)
    visited[src] = True
    frontier = np.array([src], dtype=np.int64)
    for _ in range(D):
        nb = adj[frontier].ravel()
        nb = nb[~visited[nb]]
        if nb.size == 0:
            break
        nb = np.unique(nb)
        visited[nb] = True
        frontier = nb
    return N2 - int(visited.sum())


def _cost(M, inv, S, G, D):
    """Unreached (source, vertex) pairs for the two side representatives a_e and b_e."""
    Sa = np.array(S, dtype=np.int64)
    adj = np.empty((2 * G, len(S)), dtype=np.int64)
    adj[:G] = G + M[:, Sa]
    adj[G:] = M[:, inv[Sa]]
    return _unreached(adj, 0, D, 2 * G) + _unreached(adj, G, D, 2 * G)


def _anneal(M, inv, G, d, D, rng, iters, deadline):
    """Simulated annealing over connection sets S. Returns (found, S)."""
    S = rng.sample(range(G), d)
    cur = _cost(M, inv, S, G, D)
    for t in range(iters):
        if cur == 0:
            break
        if (t & 127) == 0 and time.monotonic() > deadline:
            break
        temp = 0.5 + 2.5 * (1.0 - t / iters)
        i = rng.randrange(d)
        new_el = rng.randrange(G)
        if new_el in S:
            continue
        old = S[i]
        S[i] = new_el
        c2 = _cost(M, inv, S, G, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
        else:
            S[i] = old
    return cur == 0, S


def _haar_edges(G, M, S):
    """Edge list of the Haar graph: a_g ~ b_{g*s}."""
    edges = []
    for g in range(G):
        for s in S:
            edges.append((g, G + int(M[g, s])))
    return edges


def _search(d, D, best_n, deadline, rng, consider):
    """Grow the achieved group order with annealing; calls consider(n, edges) on each success."""
    lo = max(d, best_n // 2)
    while time.monotonic() < deadline:
        span = max(4, lo // 15)
        N = lo + 1 + rng.randrange(span)
        m, k, r = _sample_group(N, rng)
        G, M, inv = _group_tables(m, k, r)
        if G < d:
            continue
        ok, S = _anneal(M, inv, G, d, D, rng, 4000, deadline)
        if ok:
            edges = _haar_edges(G, M, S)
            n = 2 * G
            if consider(n, edges):
                lo = max(lo, G)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

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

    # Main search: Haar graphs over non-abelian groups.
    try:
        if d >= 2:
            _search(d, D, best_n, deadline, rng, consider)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
