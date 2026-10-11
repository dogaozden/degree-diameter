import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (inherited from the parent).
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
# Group voltage lifts over Z_m x| Z_k2, searched by annealing.
#
# NEW in this version:
#  * Vectorised cost. Adjacency is kept as an (N, d) numpy array `nbr`, and a
#    dart change rewrites only two column slices. Each cost evaluation is a
#    numpy BFS from the 2k orbit representatives, which is far faster than the
#    Python BFS used before. This gives many more annealing steps per second.
#  * Layer-swap move. Besides changing a voltage, a move swaps the two
#    targets of two base vertices inside one layer (a permutation layer), so
#    the base graph itself is searched, not only the voltages.
#  * Vectorised right multiplication by s in Z_m x| Z_k2, and a Moore-bound
#    early exit so calibration cases return immediately.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
_K2_CHOICES = [1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12]


def _sample_semidirect(G, rng):
    """Return (m, k2, r) with m * k2 == G giving a semidirect product Z_m x| Z_k2, or None."""
    for _ in range(60):
        k2 = rng.choice(_K2_CHOICES)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            return m, 1, 1
        for _ in range(200):
            r = rng.randrange(1, m)
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                return m, k2, r
        return m, k2, 1  # r = 1 always satisfies the relations (direct product)
    return None


def _perm_right(m, k2, pw, G, s):
    """Vector of g -> g * s for the element s = (c, dd) coded as c*k2 + dd."""
    c, dd = divmod(s, k2)
    idx = np.arange(G, dtype=np.int64)
    A = idx // k2
    B = idx % k2
    return ((A + pw[B] * c) % m) * k2 + (B + dd) % k2


def _cost_np(nbr, k, G, N, D):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid.

    Orbit representatives are A_i = i*G and B_j = (k+j)*G. Left translations are
    automorphisms, so these 2k BFS runs decide the diameter for the whole graph.
    """
    total = 0
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    for src in reps:
        reached = np.zeros(N, dtype=bool)
        reached[src] = True
        frontier = np.array([src], dtype=np.int64)
        cnt = 1
        for _ in range(D):
            cand = nbr[frontier].ravel()
            cand = cand[~reached[cand]]
            if cand.size == 0:
                break
            nxt = np.unique(cand)
            reached[nxt] = True
            cnt += nxt.size
            frontier = nxt
        total += N - cnt
    return total


def _edges_from_nbr(nbr, k, G):
    """Build (n, sorted edge list) from the adjacency array of A-vertices 0..kG-1."""
    E = set()
    for v in range(k * G):
        for w in nbr[v].tolist():
            E.add((v, w))
    return 2 * k * G, sorted(E)


def _search(d, D, k, G, rng, iters, deadline):
    """Simulated annealing over darts (voltages) and layer targets of a base graph.

    Base: k A-vertices, k B-vertices, d permutation layers. Each A_i and each B_j
    has degree exactly d. Returns (n, edges) with diameter <= D, or None.
    """
    grp = _sample_semidirect(G, rng)
    if grp is None:
        return None
    m, k2, r = grp
    pw = np.array([pow(r, b, m) for b in range(k2)], dtype=np.int64)
    N = 2 * k * G
    nd = d * k

    layers = [rng.sample(range(k), k) for _ in range(d)]  # layers[t][i] = j
    di = [0] * nd
    dj = [0] * nd
    ds = [0] * nd
    for t in range(d):
        for i in range(k):
            x = t * k + i
            di[x] = i
            dj[x] = layers[t][i]
            ds[x] = rng.randrange(G)

    P = np.zeros((nd, G), dtype=np.int64)
    Pi = np.zeros((nd, G), dtype=np.int64)
    nbr = np.zeros((N, d), dtype=np.int64)

    def set_s(x, s):
        ds[x] = s
        P[x] = _perm_right(m, k2, pw, G, s)
        Pi[x] = np.argsort(P[x])

    def write(x):
        # Dart x = t*k + i joins A_i (column t) to B_j, and B_j gets its column-t
        # neighbour from the same dart. Each column t is a perfect matching layer.
        i, j, t = di[x], dj[x], x // k
        nbr[i * G:(i + 1) * G, t] = (k + j) * G + P[x]
        nbr[(k + j) * G:(k + j + 1) * G, t] = i * G + Pi[x]

    for x in range(nd):
        set_s(x, ds[x])
        dj[x] = dj[x]
        write(x)

    def cost():
        keys = {(di[x], dj[x], ds[x]) for x in range(nd)}
        if len(keys) < nd:
            return _BIG  # parallel edges would waste degree
        return _cost_np(nbr, k, G, N, D)

    cur = cost()
    T0, Tf = 2.0, 0.05
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = max(Tf, T0 * (1.0 - it / iters))
        if k >= 2 and rng.random() < 0.25:
            # Layer-swap move: exchange the targets of two base vertices in one layer.
            t = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            x1, x2 = t * k + i1, t * k + i2
            j1, j2 = dj[x1], dj[x2]
            dj[x1], dj[x2] = j2, j1
            write(x1)
            write(x2)
            c2 = cost()
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                dj[x1], dj[x2] = j1, j2
                write(x1)
                write(x2)
        else:
            # Voltage move: change the group element of one dart.
            x = rng.randrange(nd)
            old_s = ds[x]
            old_P = P[x].copy()
            old_Pi = Pi[x].copy()
            set_s(x, rng.randrange(G))
            write(x)
            c2 = cost()
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                ds[x] = old_s
                P[x] = old_P
                Pi[x] = old_Pi
                write(x)

    if cur == 0:
        return _edges_from_nbr(nbr, k, G)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Calibration early exit: already at the Moore bound, nothing to gain.
    if best_n >= moore:
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() < deadline and best_n < moore:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: annealed group voltage lifts with 1-3 base vertices per side.
    # Target group orders just above the current best.
    while time.monotonic() < deadline and best_n < moore:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        G = max(d, 2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
        res = _search(d, D, k, G, rng, 3000, deadline)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
