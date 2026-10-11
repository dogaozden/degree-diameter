import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe exact families (kept from the parent for the other cases).
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
# New family: bi-Cayley lifts over non-metacyclic groups.
#
# Groups are given by a multiplication table M with M[g, s] = g*s.
#   - AGL(1, q) = F_q x| F_q^*  (affine maps x -> a + b x), order q(q-1).
#   - SL(2, p)  (2x2 matrices of determinant 1 mod p), order p(p^2-1).
#   - Z_m x| Z_k2 (the metacyclic family from the parent, kept as one arm).
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{j,g*s}.
# Left multiplication is an automorphism, so checking distances from one
# representative per block is an exact diameter test.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_GROUP_LIMIT = 1600


def _moore(d, D):
    """Moore bound for bipartite graphs with max degree d and diameter D."""
    if d <= 1:
        return 2
    return 2 * sum((d - 1) ** i for i in range(D))


def _agl_table(q):
    """Multiplication table of AGL(1, q); element (a, b) with b != 0 is coded as a*(q-1) + (b-1)."""
    F = lib.GF(q)
    n1 = q - 1
    G = q * n1
    x = np.arange(G, dtype=np.int64)
    a = x // n1
    b = x % n1 + 1
    add, mul = F.add_table, F.mul_table
    A1 = a[:, None]
    B1 = b[:, None]
    A2 = a[None, :]
    B2 = b[None, :]
    # (a1, b1)(a2, b2) = (a1 + b1*a2, b1*b2)
    na = add[A1, mul[B1, A2]]
    nb = mul[B1, B2]
    M = na * n1 + (nb - 1)
    return G, M.astype(np.int64)


def _sl2_table(p):
    """Multiplication table of SL(2, p) for prime p."""
    els = [(a, b, c, d) for a, b, c, d in itertools.product(range(p), repeat=4)
           if (a * d - b * c) % p == 1]
    G = len(els)
    E = np.array(els, dtype=np.int64)
    lut = np.full(p ** 4, -1, dtype=np.int64)
    lut[((E[:, 0] * p + E[:, 1]) * p + E[:, 2]) * p + E[:, 3]] = np.arange(G)
    a1, b1, c1, d1 = (E[:, t][:, None] for t in range(4))
    a2, b2, c2, d2 = (E[:, t][None, :] for t in range(4))
    na = (a1 * a2 + b1 * c2) % p
    nb = (a1 * b2 + b1 * d2) % p
    nc = (c1 * a2 + d1 * c2) % p
    nd = (c1 * b2 + d1 * d2) % p
    M = lut[((na * p + nb) * p + nc) * p + nd]
    return G, M


def _sd_table(m, k2, r):
    """Multiplication table of Z_m x| Z_k2, element a*k2 + b, (a,b)(c,e) = (a + r^b c, b + e)."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    return G, M


def _sample_sd(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
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


def _tables(M):
    """From M[g, s] = g*s build Ts[s, g] = g*s and Invs[s, h] = g with g*s = h."""
    G = M.shape[0]
    Ts = np.ascontiguousarray(M.T)
    x = np.arange(G, dtype=np.int64)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return Ts, Invs


def _candidates(d, D):
    """Non-metacyclic group candidates (kind, param, k, G, N) with N = 2kG <= Moore bound."""
    moore = _moore(d, D)
    out = []
    for q in range(3, 200):
        if not lib.is_prime_power(q):
            continue
        G = q * (q - 1)
        if G > _GROUP_LIMIT:
            break
        for k in _KS:
            N = 2 * k * G
            if N <= moore:
                out.append(("agl", q, k, G, N))
    for p in (3, 5, 7, 11):
        G = p * (p * p - 1)
        if G > _GROUP_LIMIT:
            continue
        for k in _KS:
            N = 2 * k * G
            if N <= moore:
                out.append(("sl", p, k, G, N))
    return out


def _build_group_table(c):
    kind, par = c[0], c[1]
    if kind == "agl":
        return _agl_table(par)
    return _sl2_table(par)


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for A-block i and B-block j with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b set when representative block b is within distance D."""
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


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing over layers and voltages. Returns (n, edges) or None."""
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
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

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
            if cost < best_cost:
                best_cost, last_improve = cost, t
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


def _pick_group(k, best_n, d, D, cands, rng):
    """Return (G, Ts, Invs) for a group arm with base size k, or None."""
    if rng.random() < 0.6:
        pool = [c for c in cands if c[2] == k and c[4] > best_n]
        if pool:
            hi = max(best_n * 1.15, best_n + 40)
            near = [c for c in pool if c[4] <= hi]
            if near:
                c = rng.choice(near)
            else:
                lo = min(c[4] for c in pool)
                c = rng.choice([c for c in pool if c[4] == lo])
            G, M = _build_group_table(c)
            Ts, Invs = _tables(M)
            return G, Ts, Invs
    base = best_n // (2 * k)
    target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
    g = _sample_sd(target, rng)
    if g is None:
        return None
    m, k2, r = g
    G, M = _sd_table(m, k2, r)
    Ts, Invs = _tables(M)
    return G, Ts, Invs


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, time_limit - 8.0)
    final_deadline = start + max(1.0, time_limit - 4.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Exact constructions for the calibration-style cases.
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

    # Bold search: group bi-Cayley lifts over AGL(1,q), SL(2,p) and the metacyclic family.
    moore = _moore(d, D)
    cands = _candidates(d, D)
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        built = _pick_group(k, best_n, d, D, cands, rng)
        if built is None:
            continue
        G, Ts, Invs = built
        N = 2 * k * G
        if N <= best_n or N > moore or G > _GROUP_LIMIT + 400:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 6000, 1500)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D) or time.monotonic() > final_deadline + 3.0:
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
    return best
