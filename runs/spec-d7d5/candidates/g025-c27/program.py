import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / safe baseline families (kept from the parent for calibration and D=3,4).
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _araujo_for(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New construction: bipartite Cayley graphs (base size 1) over finite groups.
#
# Vertices A_g = g and B_h = G + h. Layer i with distinct generator s_i joins
# A_g to B_{g*s_i}. Left multiplication is an automorphism, so the graph has
# diameter <= D iff every vertex is within D of A_e and of B_e. This makes the
# cost a cheap pair of BFS runs.
#
# Groups: cyclic and semidirect products Z_m x| Z_k2 (order in a target window),
# plus PSL(2,p) for p = 11, 13 (orders 660, 1092), which are non-metabelian and
# not reachable by the parent's block lifts.
# ----------------------------------------------------------------------------

_PSL_CACHE = {}


def _semidirect_group(m, k2, r):
    """Return (G, M, inv, e) for Z_m x| Z_k2 with identity index 0."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    inv = np.empty(G, dtype=np.int64)
    rows, cols = np.nonzero(M == 0)
    inv[rows] = cols
    return G, M, inv, 0


def _psl_group(p):
    """Return (G, M, inv, e) for PSL(2, p) with elements normalised up to sign."""
    if p in _PSL_CACHE:
        return _PSL_CACHE[p]

    def key(x0, x1, x2, x3):
        return ((x0 * p + x1) * p + x2) * p + x3

    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    a, b, c, dd = allm[:, 0], allm[:, 1], allm[:, 2], allm[:, 3]
    E = allm[(a * dd - b * c) % p == 1]
    negE = (-E) % p
    nk = np.minimum(key(E[:, 0], E[:, 1], E[:, 2], E[:, 3]),
                    key(negE[:, 0], negE[:, 1], negE[:, 2], negE[:, 3]))
    reps = np.unique(nk)
    G = len(reps)
    E2 = np.stack([reps // p**3, (reps // p**2) % p, (reps // p) % p, reps % p], axis=1)
    lookup = np.full(p**4, -1, dtype=np.int64)
    lookup[reps] = np.arange(G)

    A = E2[:, None, :]
    B = E2[None, :, :]
    pa = (A[..., 0] * B[..., 0] + A[..., 1] * B[..., 2]) % p
    pb = (A[..., 0] * B[..., 1] + A[..., 1] * B[..., 3]) % p
    pc = (A[..., 2] * B[..., 0] + A[..., 3] * B[..., 2]) % p
    pd = (A[..., 2] * B[..., 1] + A[..., 3] * B[..., 3]) % p
    K = key(pa, pb, pc, pd)
    Kn = key((-pa) % p, (-pb) % p, (-pc) % p, (-pd) % p)
    M = lookup[np.minimum(K, Kn)]

    e = int(lookup[key(1, 0, 0, 1)])
    inv = np.empty(G, dtype=np.int64)
    rows, cols = np.nonzero(M == e)
    inv[rows] = cols
    res = (G, M, inv, e)
    _PSL_CACHE[p] = res
    return res


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24])
        m = max(2, -(-target // k2))
        if k2 == 1:
            return m, 1, 1
        if k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) == 1 and pow(r, 2, m) == 1 % m:
                return m, 2, r
            continue
        for _ in range(60):
            c = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                return m, k2, c
    return None


def _pick_group(lo, rng):
    """Pick a group of order at least lo (the bi-Cayley graph then has 2G vertices)."""
    if lo > 1400:
        return None
    u = rng.random()
    if u < 0.2 and lo <= 660:
        return _psl_group(11)
    if u < 0.25 and lo <= 1092:
        return _psl_group(13)
    target = lo + rng.randrange(0, max(2, lo // 8))
    g = _sample_group(target, rng)
    if g is None:
        return None
    m, k2, r = g
    if m * k2 > 1400:
        return None
    return _semidirect_group(m, k2, r)


def _set_layer(nbr, G, M, inv, i, s):
    """Layer i uses generator s: A_g ~ B_{g s}, equivalently B_h ~ A_{h s^-1}."""
    nbr[i, :G] = G + M[:, s]
    nbr[i, G:] = M[:, inv[s]]


def _unreached(nbr, src, D, N):
    """Number of vertices at distance > D from src (BFS over the whole graph)."""
    dist = np.full(N, -1, dtype=np.int64)
    dist[src] = 0
    frontier = np.array([src], dtype=np.int64)
    for t in range(1, D + 1):
        nb = nbr[:, frontier].ravel()
        nb = np.unique(nb[dist[nb] < 0])
        if nb.size == 0:
            break
        dist[nb] = t
        frontier = nb
    return int(np.count_nonzero(dist < 0))


def _search(d, D, G, M, inv, e, rng, deadline, iters, patience):
    """Simulated annealing over the d distinct generators. Returns (n, edges) or None."""
    N = 2 * G
    s = rng.sample(range(G), d)
    nbr = np.empty((d, N), dtype=np.int64)
    for i in range(d):
        _set_layer(nbr, G, M, inv, i, s[i])

    def cost():
        return _unreached(nbr, e, D, N) + _unreached(nbr, G + e, D, N)

    c = cost()
    c0 = float(max(c, 1))
    best = c
    last = 0
    for t in range(iters):
        if c == 0 or time.monotonic() > deadline or t - last > patience:
            break
        temp = max(0.3, 0.03 * c0 * (1.0 - t / iters))
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in s:
            continue
        old = s[i]
        s[i] = new
        _set_layer(nbr, G, M, inv, i, new)
        c2 = cost()
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            c = c2
            if c < best:
                best = c
                last = t
        else:
            s[i] = old
            _set_layer(nbr, G, M, inv, i, old)
    if c != 0:
        return None
    edges = []
    for i in range(d):
        for g in range(G):
            edges.append((g, G + int(M[g, s[i]])))
    return N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions for D = 3 and D = 4.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
        if D == 3:
            ar = _araujo_for(d)
            if ar is not None:
                consider(ar[0], ar[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: bi-Cayley graphs over varied groups, targeting order above the incumbent.
    while time.monotonic() < deadline:
        lo = best_n // 2 + 1
        if lo > 1400:
            break
        grp = _pick_group(lo, rng)
        if grp is None:
            continue
        G, M, inv, e = grp
        if G < d or 2 * G <= best_n:
            continue
        res = _search(d, D, G, M, inv, e, rng, deadline, 6000, 1500)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
