import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact baselines (used when they are optimal or as safe fallbacks).
# ----------------------------------------------------------------------------

_GQ_MAX_Q = 7


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
    """W(q) for the largest prime power q with q + 1 <= d, capped for speed."""
    for q in range(min(d - 1, _GQ_MAX_Q), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-regular lifts over finite groups.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A-block i with B-block layers[l][i] through voltage s:
#     A_{i,g} ~ B_{p,g*s},   B_{p,h} ~ A_{i,h*s^-1}.
# Every layer is a permutation of blocks, so degrees are d.
#
# Groups used (new in this version): abelian non-cyclic Z_a x Z_b, and
# semidirect products Z_m x| Z_k (including dihedral-type with r = -1).
# Each group is given by a G x G table M[g,s] = g*s with identity 0, so the
# same lift machinery works for every family.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4, 5, 6)
_GMAX = 1400
_K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24]
_AB_CHOICES = [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 27, 28, 30, 32, 36]


def _table_from_product(G, M):
    """Return (G, Ts, Invs) from M[g, s] = g*s. Ts[s, g] = g*s; Invs[s, h] = g with g*s = h."""
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    x = np.arange(G, dtype=np.int64)
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _abelian(a, b):
    """Z_a x Z_b, element i*b + j, identity 0."""
    G = a * b
    x = np.arange(G, dtype=np.int64)
    i = x // b
    j = x % b
    M = ((i[:, None] + i[None, :]) % a) * b + (j[:, None] + j[None, :]) % b
    return _table_from_product(G, M)


def _semidirect(m, k2, r):
    """Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e), element a*k2 + b, identity 0."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    return _table_from_product(G, M)


def _sample_group(target, rng):
    """Return a group spec with order >= target (and <= _GMAX), or None."""
    for _ in range(300):
        x = rng.random()
        if x < 0.4:
            k2 = rng.choice(_K2_CHOICES)
            m = max(2, -(-target // k2))
            if k2 == 1:
                r = 1
            else:
                r = None
                if k2 == 2 and rng.random() < 0.5:
                    r = m - 1
                else:
                    for _ in range(60):
                        c = rng.randrange(2, m) if m > 2 else 1
                        if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                            r = c
                            break
                if r is None:
                    continue
            if m * k2 > _GMAX:
                continue
            return ("semi", m, k2, r)
        elif x < 0.8:
            b = rng.choice(_AB_CHOICES)
            a = max(2, -(-target // b))
            if a * b > _GMAX:
                continue
            return ("ab", a, b)
        else:
            m = max(3, -(-target // 2))
            if 2 * m > _GMAX:
                continue
            return ("semi", m, 2, m - 1)
    return None


def _build_group(spec):
    if spec[0] == "semi":
        _, m, k2, r = spec
        return _semidirect(m, k2, r)
    _, a, b = spec
    return _abelian(a, b)


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for A-block i and B-block j with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b set when representative of block b is within distance D."""
    N = nbr.shape[1]
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
    return reach


def _unreached(k, N, reach):
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over voltages and layer swaps. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))

        if k >= 2 and rng.random() < 0.25:
            # Layer swap: exchange B-targets of two A-blocks in one layer.
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        # Voltage move: defect-targeted with probability 0.4, otherwise uniform.
        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = []
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.append((u, int(v)))
    return N, edges


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

    # Exact constructions (calibration-style cases return immediately).
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
            if D == 4 and d - 1 <= _GQ_MAX_Q and lib.is_prime_power(d - 1):
                return best

    # Main search: bandit over base sizes k, mixed group families.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        base_target = best_n // (2 * k) + 1
        slack = max(1, base_target // 10)
        target = base_target + rng.randrange(0, slack + 1)
        spec = _sample_group(target, rng)
        if spec is None:
            continue
        G, Ts, Invs = _build_group(spec)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 3000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
