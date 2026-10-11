import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# Group tables for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).
# Identity is index 0.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4)
_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_SWAP_PROB = 0.3
_STRUCT_PROB = 0.5
_HAAR_ITERS = 3000


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))  # ceil, so the order is at least target
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


def _pick_group(target, rng):
    """Return (m, k2, r) with m*k2 >= target for a semidirect product, mostly non-abelian. Or None."""
    for _ in range(300):
        k2 = rng.choice([1, 2, 2, 3, 4, 4, 5, 6, 8, 9, 10, 12, 16])
        m = max(2, -(-target // k2)) + rng.randrange(0, 4)
        if m < 3 and k2 > 1:
            continue
        if k2 == 1 or rng.random() < 0.2:
            r = 1
        else:
            r = None
            for _ in range(80):
                c = rng.randrange(2, m)
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h, built with one numpy broadcast.
    """
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = M[g, s] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


# ----------------------------------------------------------------------------
# NEW ENGINE (target d=7, D=5): single-layer Haar graphs over semidirect groups.
#
# Haar graph H(G, S): a_g ~ b_{g*s} for s in S, |S| = d, G of order N.
# Left multiplication is an automorphism, transitive on each side, so the
# diameter is at most D iff the balls of radius D around a_e and b_e cover
# everything. Cost = number of unreached (source, vertex) pairs, minimised by
# simulated annealing over the d-element connection set S.
# Order of the graph is 2N; target is N >= 568 (record 1134 = 2*567).
# ----------------------------------------------------------------------------

def _haar_cost(S, Ts, Invs, N, D):
    """Unreached (source, vertex) pairs for sources a_e (row 0) and b_e (row 1)."""
    TsS = Ts[S]
    InvS = Invs[S]
    SA = np.zeros((2, N), dtype=bool)  # A-side vertices within current radius
    SB = np.zeros((2, N), dtype=bool)  # B-side vertices within current radius
    SA[0, 0] = True
    SB[1, 0] = True
    for _ in range(D):
        nB = SA[:, InvS].any(axis=1)  # b_h adjacent to a_g with g*s = h
        nA = SB[:, TsS].any(axis=1)   # a_g adjacent to b_{g*s}
        SA |= nA
        SB |= nB
    return 4 * N - int(SA.sum()) - int(SB.sum())


def _haar_phase(d, D, rng, deadline, target):
    """Anneal Haar-graph connection sets over groups of order >= target. Returns (n, edges) or None."""
    best = None
    while time.monotonic() < deadline:
        grp = _pick_group(target, rng)
        if grp is None:
            continue
        m, k2, r = grp
        N, Ts, Invs = _semidirect_tables(m, k2, r)
        if N < d:
            continue
        S = rng.sample(range(N), d)
        c = _haar_cost(np.array(S, dtype=np.int64), Ts, Invs, N, D)
        T0 = max(1.0, 0.05 * c)
        for t in range(_HAAR_ITERS):
            if c == 0 or time.monotonic() > deadline:
                break
            temp = 0.3 + T0 * (1.0 - t / _HAAR_ITERS)
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in S:
                continue
            old = S[i]
            S[i] = x
            c2 = _haar_cost(np.array(S, dtype=np.int64), Ts, Invs, N, D)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
                c = c2
            else:
                S[i] = old
        if c != 0:
            continue
        edges = [(gg, N + int(Ts[s, gg])) for gg in range(N) for s in S]
        n = 2 * N
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
            target = N + 1  # ratchet: only look for strictly larger groups now
    return best


# ----------------------------------------------------------------------------
# Previous engine: bi-Cayley lifts with several base blocks (kept as the
# general-purpose search and as the fallback for other cases).
# ----------------------------------------------------------------------------

def _structured_init(d, k, G, Ts, rng):
    """Geometric-progression start: layers[l][i] = (i + l) mod k, S[l][i] = y_i * x^(l+1)."""
    x = rng.randrange(1, G)
    powers = [0]  # identity element is index 0
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
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


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


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer target swaps. Returns (n, edges) or None."""
    N = 2 * k * G
    if rng.random() < _STRUCT_PROB:
        layers, S = _structured_init(d, k, G, Ts, rng)
    else:
        layers, S = _random_init(d, k, G, rng)
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    cost = _cost(k, G, D, nbr) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)

        if k > 1 and rng.random() < _SWAP_PROB:
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            c2 = _cost(k, G, D, nbr) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        i = rng.randrange(k)
        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        c2 = _cost(k, G, D, nbr) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def _legacy(d, D, rng, deadline, best):
    """Exact constructions plus the bandit bi-Cayley search. Only accepts strictly larger valid graphs."""
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

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
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
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    return best


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

    # Bold new route for the target case: single-layer Haar graphs over
    # non-abelian semidirect groups, annealed for diameter 5.
    if d == 7 and D == 5:
        hb = _haar_phase(d, D, rng, start + 0.5 * budget, 568)
        if hb is not None and hb[0] > best[0] and lib.is_valid(hb[0], hb[1], d, D):
            best = hb

    best = _legacy(d, D, rng, deadline, best)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
