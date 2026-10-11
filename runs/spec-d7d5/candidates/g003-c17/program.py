import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact and safe baseline families.
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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2, searched by annealing.
#
# Base graph: k vertices per side. Vertices A_{i,g} = i*G + g and
# B_{j,h} = (k+j)*G + h. Layer l is a permutation layers[l] of range(k)
# together with voltages S[l][i]: A_{i,g} ~ B_{perm[i], g*s}. Every vertex
# gets degree d. Left multiplication is an automorphism, so the diameter
# check only needs the 2k identity vertices, done bit-parallel.
#
# Moves: change one voltage, or swap two targets within one layer. Both keep
# the graph d-regular. Duplicate-edge conflicts are penalised.
# ----------------------------------------------------------------------------

_PEN = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _semi(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 with (a, b)*(c, d) = (a + r^b c, b + d).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h. Element (a, b) is coded a*k2 + b.
    """
    G = m * k2
    pw = np.array([pow(r, b, m) for b in range(k2)], dtype=np.int64)
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _sample(T, rng):
    """Return (m, k2, r) with group order m*k2 near T, using a valid unit r with r^k2 = 1 mod m."""
    k2 = rng.choice([1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24])
    m = max(2, T // k2)
    if k2 == 1:
        return m, 1, 1
    if m <= 2 or rng.random() < 0.4:
        return m, k2, 1
    for _ in range(80):
        c = rng.randrange(2, m)
        if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
            return m, k2, c
    return m, k2, 1


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for A base vertex i and B base vertex j with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _cost(k, G, D, nbr):
    """Count unreached (identity representative, vertex) pairs within distance D."""
    d, N = nbr.shape
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return 2 * k * N - int(_POP[reach].sum())


def _anneal(d, D, k, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over permutations and voltages. Returns (n, edges) or None."""
    N = 2 * k * G
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dup():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    def total():
        return _cost(k, G, D, nbr) + _PEN * dup()

    cost = total()
    c0 = float(max(cost, 1))
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.3, 0.03 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)
        if k < 2 or rng.random() < 0.5:
            # Voltage move.
            i = rng.randrange(k)
            old = S[l][i]
            new = rng.randrange(G)
            if new == old:
                continue
            S[l][i] = new
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
            c2 = total()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                S[l][i] = old
                _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)
        else:
            # Swap move: exchange the B targets of two A vertices in one layer.
            i, i2 = rng.sample(range(k), 2)
            layers[l][i], layers[l][i2] = layers[l][i2], layers[l][i]
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            c2 = total()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                layers[l][i], layers[l][i2] = layers[l][i2], layers[l][i]
                _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])

    if cost != 0:
        return None
    cols = nbr[:, :k * G].T.tolist()
    edges = [(u, v) for u in range(k * G) for v in cols[u]]
    return N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 8.0))
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

    # Exact constructions for calibration-style cases.
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

    # Main search: annealed bi-Cayley lifts with up to 6 base vertices per side.
    while time.monotonic() < deadline:
        k = rng.choice([1, 2, 2, 3, 3, 4, 5, 6])
        T = best_n // (2 * k) + 1 + rng.randrange(0, 3)
        m, k2, r = _sample(max(2, T), rng)
        G, Ts, Invs = _semi(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        res = _anneal(d, D, k, G, Ts, Invs, rng, deadline, 25000)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
