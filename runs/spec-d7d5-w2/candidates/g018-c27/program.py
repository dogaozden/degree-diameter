import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / safe baseline families (used for calibration-style cases and as
# fallbacks).
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
# Different construction: multi-block bi-Cayley lifts over semidirect products
# Z_m x| Z_k2 (order G), searched by simulated annealing with a BFS-based cost.
#
# Vertices: A_{i,g} = i*G + g, B_{j,h} = (k+j)*G + h, group elements coded a*k2+b.
# In layer l, A-block i is matched to B-block p[l][i] by the voltage s[l][i]:
#     A_{i,g} ~ B_{p, g*s},     equivalently  B_{j,h} ~ A_{i, h*s^-1}.
# Each layer is a perfect matching of blocks, so every vertex has degree d and
# the graph is bipartite by construction. Distinct (i, p, s) keys avoid
# parallel edges.
#
# Left multiplication is an automorphism, so distances only need checking from
# the 2k block representatives (identity of each block).
# ----------------------------------------------------------------------------

_PEN = 1000


def _groups(G):
    """All (m, k2, r) with m * k2 = G, k2 <= 16, giving Z_m x| Z_k2 (r^k2 = 1 mod m, gcd(r, m) = 1)."""
    out = []
    for k2 in range(1, 17):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    return out


def _tables(m, k2, r):
    """Multiplication table M[x, y] = x*y and right-inverse table Minv[s] = s^-1 for the semidirect product."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    pw = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Minv = (M == 0).argmax(axis=1).astype(np.int64)
    return M, Minv


def _unreached(nbr, N, srcs, D):
    """Total number of (source, vertex) pairs not within distance D, over the given sources."""
    total = 0
    for src in srcs:
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            nxt = nbr[:, front].ravel()
            nxt = np.unique(nxt[~seen[nxt]])
            if nxt.size == 0:
                break
            seen[nxt] = True
            front = nxt
        total += N - int(seen.sum())
    return total


def _anneal(d, D, k, G, M, Minv, rng, deadline, iters):
    """Simulated annealing over voltages and block matchings. Returns (n, edges) or None."""
    N = 2 * k * G
    srcs = [b * G for b in range(2 * k)]
    p = [rng.sample(range(k), k) for _ in range(d)]
    s = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)

    def setdart(l, i):
        j = p[l][i]
        v = s[l][i]
        nbr[l, i * G:(i + 1) * G] = (k + j) * G + M[:, v]
        nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + M[:, Minv[v]]

    for l in range(d):
        for i in range(k):
            setdart(l, i)

    def dup():
        keys = {(i, p[l][i], s[l][i]) for l in range(d) for i in range(k)}
        return d * k - len(keys)

    def cost_now():
        return _unreached(nbr, N, srcs, D) + _PEN * dup()

    cost = cost_now()
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = 0.3 + 3.0 * (1.0 - t / iters)
        if k >= 2 and rng.random() < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            p[l][i1], p[l][i2] = p[l][i2], p[l][i1]
            setdart(l, i1)
            setdart(l, i2)
            c2 = cost_now()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                p[l][i1], p[l][i2] = p[l][i2], p[l][i1]
                setdart(l, i1)
                setdart(l, i2)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)
            old = s[l][i]
            new = rng.randrange(G)
            if new == old:
                continue
            s[l][i] = new
            setdart(l, i)
            c2 = cost_now()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                s[l][i] = old
                setdart(l, i)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            v = int(v)
            edges.add((u, v) if u < v else (v, u))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
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

    # Exact constructions for calibration-style cases.
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

    # Main search: annealed multi-block lifts over semidirect products,
    # always targeting orders just above the current best.
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 3))
        lo = best_n // (2 * k) + 1
        G = lo + rng.randrange(0, max(2, lo // 40))
        G = max(G, 2)
        cands = _groups(G)
        if not cands:
            continue
        m, k2, r = rng.choice(cands)
        M, Minv = _tables(m, k2, r)
        res = _anneal(d, D, k, G, M, Minv, rng, deadline, 6000)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
