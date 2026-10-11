import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (exact constructions and small generalized polygons).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power >= 3, else None."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2.
#
# Changed search: instead of blind simulated annealing, each step rewires one
# dart to the best of a random sample of candidate voltages (steepest-descent
# style on the coverage cost), with occasional target swaps and random uphill
# acceptance. Stalled runs restart from a fresh start.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_CANDIDATES = 40
_SWAP_PROB = 0.25
_STRUCT_PROB = 0.5
_STALL_LIMIT = 400
_UPHILL_PROB = 0.03


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h.
    """
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _structured_init(d, k, G, Ts, rng):
    """Geometric-progression start: layers[l][i] = (i + l) mod k, S[l][i] = y_i * x^(l+1)."""
    x = rng.randrange(1, G)
    powers = [0]
    for _ in range(d):
        powers.append(int(Ts[x, powers[-1]]))
    ys = [rng.randrange(G) for _ in range(k)]
    layers = [[(i + l) % k for i in range(k)] for l in range(d)]
    S = [[int(Ts[ys[i], powers[l + 1]]) for i in range(k)] for l in range(d)]
    return layers, S


def _random_init(d, k, G, rng):
    """Uniform start: random permutation per layer and random voltages."""
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    return layers, S


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for A-vertex i and B-vertex j with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _dup(layers, S, d, k):
    """Number of repeated (A-vertex, target, voltage) darts."""
    keys = set()
    dup = 0
    for l in range(d):
        for i in range(k):
            key = (i, layers[l][i], S[l][i])
            if key in keys:
                dup += 1
            else:
                keys.add(key)
    return dup


def _cost(k, G, D, nbr):
    """Unreached (representative, vertex) pairs over all 2k representatives."""
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


_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _search(d, D, k, G, Ts, Invs, rng, deadline):
    """Greedy best-candidate rewiring with restarts. Returns (n, edges) or None."""
    N = 2 * k * G

    def full_cost():
        return _cost(k, G, D, nbr) + _PENALTY * _dup(layers, S, d, k)

    while time.monotonic() < deadline:
        if rng.random() < _STRUCT_PROB:
            layers, S = _structured_init(d, k, G, Ts, rng)
        else:
            layers, S = _random_init(d, k, G, rng)
        nbr = np.empty((d, N), dtype=np.int64)
        for l in range(d):
            for i in range(k):
                _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

        cost = full_cost()
        best_seen = cost
        stall = 0

        while cost > 0 and stall < _STALL_LIMIT and time.monotonic() < deadline:
            l = rng.randrange(d)
            i = rng.randrange(k)

            if k > 1 and rng.random() < _SWAP_PROB:
                # Swap B-side targets of two A-vertices in layer l (voltages kept).
                i2 = rng.randrange(k - 1)
                if i2 >= i:
                    i2 += 1
                layers[l][i], layers[l][i2] = layers[l][i2], layers[l][i]
                _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
                c2 = full_cost()
                if c2 <= cost or rng.random() < _UPHILL_PROB:
                    cost = c2
                else:
                    layers[l][i], layers[l][i2] = layers[l][i2], layers[l][i]
                    _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])
                    _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            else:
                # Voltage rewire: evaluate a sample of voltages, keep the best.
                old = S[l][i]
                best_c, best_s = None, None
                for _ in range(_CANDIDATES):
                    s = rng.randrange(G)
                    if s == old:
                        continue
                    S[l][i] = s
                    _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], s)
                    c = full_cost()
                    if best_c is None or c < best_c or (c == best_c and rng.random() < 0.5):
                        best_c, best_s = c, s
                if best_s is None:
                    S[l][i] = old
                    _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)
                    continue
                if best_c <= cost or rng.random() < _UPHILL_PROB:
                    S[l][i] = best_s
                    _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], best_s)
                    cost = best_c
                else:
                    S[l][i] = old
                    _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

            if cost < best_seen:
                best_seen = cost
                stall = 0
            else:
                stall += 1

        if cost == 0:
            edges = set()
            for u in range(k * G):
                for v in nbr[:, u]:
                    edges.add((u, int(v)))
            return N, sorted(edges)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.9 * time_limit, time_limit - 5.0))
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

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 3:
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: bandit over base sizes k, with per-attempt time slices.
    ks = (1, 2, 3, 4)
    trials = {k: 0 for k in ks}
    wins = {k: 0 for k in ks}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(ks)
        return max(ks, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    slice_len = max(4.0, budget * 0.2)
    while time.monotonic() < deadline - 0.5:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        attempt_deadline = min(deadline, time.monotonic() + slice_len)
        res = _search(d, D, k, G, Ts, Invs, rng, attempt_deadline)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
