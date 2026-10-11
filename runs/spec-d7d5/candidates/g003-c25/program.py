import itertools
import math
import random
import time

import numpy as np

import lib


_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_MAX_G = 1200


# ----------------------------------------------------------------------------
# Exact and near-exact baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (q kept small)."""
    for q in range(d - 1, 1, -1):
        if q > 40:
            continue
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo and Lopez record graph for d = q + 2 with q a prime power."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except Exception:
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
# Group families. Each returns (G, RT) with RT[s, g] = g * s and identity at
# index 0. Left multiplication is an automorphism, so block representatives
# at the identity of each side cover all vertex orbits.
# ----------------------------------------------------------------------------

def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def _primitive_root(p):
    phi = p - 1
    factors = []
    x = phi
    f = 2
    while f * f <= x:
        if x % f == 0:
            factors.append(f)
            while x % f == 0:
                x //= f
        f += 1
    if x > 1:
        factors.append(x)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in factors):
            return g
    return 1


def _affine_table(p, t):
    """Affine group {x -> a x + b over Z_p : a in H}, |H| = t, t | p-1. Order p*t, identity at 0."""
    g0 = _primitive_root(p)
    h = pow(g0, (p - 1) // t, p)
    H = [pow(h, j, p) for j in range(t)]
    pos = np.full(p, -1, dtype=np.int64)
    for i, v in enumerate(H):
        pos[v] = i
    G = p * t
    idx = np.arange(G, dtype=np.int64)
    Hv = np.array(H, dtype=np.int64)
    A = Hv[idx // p]
    B = idx % p
    RT = np.empty((G, G), dtype=np.int64)
    for s in range(G):
        a2 = H[s // p]
        b2 = s % p
        na = (A * a2) % p
        nb = (A * b2 + B) % p
        RT[s] = pos[na] * p + nb
    return G, RT


def _semidirect_table(m, k, r):
    """Z_m x|_r Z_k with (a1,b1)(a2,b2) = (a1 + r^{b1} a2, b1 + b2); element (a,b) coded a*k+b."""
    G = m * k
    idx = np.arange(G, dtype=np.int64)
    A = idx // k
    B = idx % k
    powr = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    PB = powr[B]
    RT = np.empty((G, G), dtype=np.int64)
    for s in range(G):
        c, dd = divmod(s, k)
        RT[s] = ((A + PB * c) % m) * k + (B + dd) % k
    return G, RT


def _group_options(G, rng):
    """Candidate group descriptions of order exactly G (cyclic is always included)."""
    opts = [("semi", G, 1, 1)]
    for k2 in range(2, min(G, 24) + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if rs:
            for r in rng.sample(rs, min(3, len(rs))):
                opts.append(("semi", m, k2, r))
    for t in range(1, G + 1):
        if G % t:
            continue
        p = G // t
        if p >= 3 and _is_prime(p) and (p - 1) % t == 0:
            opts.append(("aff", p, t))
    return opts


def _table(opt):
    if opt[0] == "aff":
        return _affine_table(opt[1], opt[2])
    _, m, k2, r = opt
    return _semidirect_table(m, k2, r)


def _inverse_table(G, RT):
    """Invs[s, h] = the g with g * s = h."""
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, RT] = np.arange(G)[None, :]
    return Invs


# ----------------------------------------------------------------------------
# Bi-Cayley lift search. Base: k vertices per side, d layers. Layer l is a
# permutation layers[l] of range(k) plus a voltage S[l][i] per A-vertex i:
# A_{i,g} ~ B_{layers[l][i], g*s}. Each vertex then has degree d.
# Cost = unreached (representative, vertex) pairs within distance D, computed
# with bit-parallel propagation over the 2k representatives.
# ----------------------------------------------------------------------------

def _set_dart(nbr, k, G, RT, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + RT[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _cost(k, G, D, nbr):
    d, N = nbr.shape
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] |= (1 << b)
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, RT, Invs, rng, deadline, iters):
    """Simulated annealing over voltages and layer permutations. Returns (n, edges) or None."""
    N = 2 * k * G
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, RT, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = set()
        dups = 0
        for l in range(d):
            for i in range(k):
                key = (i, layers[l][i], S[l][i])
                if key in keys:
                    dups += 1
                else:
                    keys.add(key)
        return dups

    cost = _cost(k, G, D, nbr) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.3, 0.02 * c0 * (1.0 - t / iters))

        if k > 1 and rng.random() < 0.25:
            # Swap the targets of two A-vertices in one layer.
            l = rng.randrange(d)
            i, i2 = rng.sample(range(k), 2)
            layers[l][i], layers[l][i2] = layers[l][i2], layers[l][i]
            _set_dart(nbr, k, G, RT, Invs, l, i, layers[l][i], S[l][i])
            _set_dart(nbr, k, G, RT, Invs, l, i2, layers[l][i2], S[l][i2])
            c2 = _cost(k, G, D, nbr) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                layers[l][i], layers[l][i2] = layers[l][i2], layers[l][i]
                _set_dart(nbr, k, G, RT, Invs, l, i, layers[l][i], S[l][i])
                _set_dart(nbr, k, G, RT, Invs, l, i2, layers[l][i2], S[l][i2])
        else:
            # Change one voltage.
            l = rng.randrange(d)
            i = rng.randrange(k)
            old = S[l][i]
            new = rng.randrange(G)
            if new == old:
                continue
            S[l][i] = new
            _set_dart(nbr, k, G, RT, Invs, l, i, layers[l][i], new)
            c2 = _cost(k, G, D, nbr) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                S[l][i] = old
                _set_dart(nbr, k, G, RT, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = []
    for u in range(k * G):
        for v in nbr[:, u].tolist():
            edges.append((u, v))
    return N, edges


# ----------------------------------------------------------------------------
# Entry point.
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

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3:
            if pg is not None and lib.is_prime_power(d - 1):
                return best
            ara = _araujo(d)
            if ara is not None:
                consider(ara[0], ara[1])

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: bi-Cayley lifts over cyclic, semidirect and affine groups.
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 2, 2, 3, 4])
        base = best[0] // (2 * k)
        span = max(3, base // 10 + 2)
        G = base + 1 + rng.randrange(span)
        if G < 2 or G > _MAX_G:
            continue
        opts = _group_options(G, rng)
        if not opts:
            continue
        opt = rng.choice(opts)
        G2, RT = _table(opt)
        Invs = _inverse_table(G2, RT)
        res = _search(d, D, k, G2, RT, Invs, rng, deadline, 3000)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
