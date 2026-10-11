import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (exact constructions for small D).
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
# Bi-Cayley lifts over a WIDER family of finite groups.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
# Every layer is a permutation, so every vertex gets degree d.
# Left multiplication is an automorphism for ANY group, so the cost only needs
# 2k representatives.
#
# Groups used (all with identity at index 0):
#   semi : Z_m x| Z_k2 (cyclic normal subgroup)
#   agl  : affine group AGL(1,p) = Z_p x| Z_p^*, order p(p-1), non-cyclic-normal
#   dih  : dihedral group of order 2m
#   ab   : non-cyclic abelian Z_a x Z_b
# The search itself is simulated annealing over voltages and per-layer target
# swaps, with a bandit over base sizes k.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4, 5, 6)
_SWAP_PROB = 0.3
_STRUCT_PROB = 0.5
_SLICE = 6.0
_ITERS = 4000
_MAX_G = 2500
_PRIMES = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]
_K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36]


def _grp_semi(m, k2, r):
    """Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e). Returns (G, M) with M[g,h] = g*h."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    return G, M


def _grp_agl(p):
    """AGL(1,p): maps x -> u x + t. Element t*(p-1)+(u-1). Returns (G, M)."""
    G = p * (p - 1)
    x = np.arange(G, dtype=np.int64)
    t = x // (p - 1)
    u = x % (p - 1) + 1
    tt = (u[:, None] * t[None, :] + t[:, None]) % p
    uu = (u[:, None] * u[None, :]) % p
    M = tt * (p - 1) + (uu - 1)
    return G, M


def _grp_dih(m):
    """Dihedral group of order 2m, element r*2+f. Returns (G, M)."""
    G = 2 * m
    x = np.arange(G, dtype=np.int64)
    r = x // 2
    f = x % 2
    sign = np.where(f[:, None] == 1, -1, 1).astype(np.int64)
    rr = (r[:, None] + sign * r[None, :]) % m
    ff = (f[:, None] + f[None, :]) % 2
    M = rr * 2 + ff
    return G, M


def _grp_ab(a, b):
    """Abelian Z_a x Z_b, element x*b+y. Returns (G, M)."""
    G = a * b
    x = np.arange(G, dtype=np.int64)
    p = x // b
    q = x % b
    M = ((p[:, None] + p[None, :]) % a) * b + (q[:, None] + q[None, :]) % b
    return G, M


def _sample_group(lo, rng):
    """Return a group spec with order >= lo, or None."""
    fam = rng.choice(["semi", "semi", "semi", "agl", "dih", "ab"])
    if fam == "semi":
        for _ in range(100):
            k2 = rng.choice(_K2_CHOICES)
            m = max(2, -(-lo // k2))
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
            return ("semi", m, k2, r)
        return None
    if fam == "agl":
        cands = [p for p in _PRIMES if lo <= p * (p - 1) <= lo + max(4, lo // 8)]
        if not cands:
            return None
        return ("agl", rng.choice(cands))
    if fam == "dih":
        return ("dih", max(2, -(-lo // 2)))
    a = rng.choice([2, 3, 4, 5, 6, 8])
    b = max(2, -(-lo // a))
    return ("ab", a, b)


def _table(spec):
    kind = spec[0]
    if kind == "semi":
        return _grp_semi(spec[1], spec[2], spec[3])
    if kind == "agl":
        return _grp_agl(spec[1])
    if kind == "dih":
        return _grp_dih(spec[1])
    return _grp_ab(spec[1], spec[2])


def _ts_invs(G, M):
    """Ts[s, g] = g*s, Invs[s, h] = the g with g*s = h."""
    Ts = np.ascontiguousarray(M.T)
    x = np.arange(G, dtype=np.int64)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return Ts, Invs


def _structured_init(d, k, G, Ts, rng):
    """Geometric-progression start: layers[l][i] = (i + l) mod k, S[l][i] = y_i * x^(l+1)."""
    x = rng.randrange(1, G)
    powers = [0]  # identity element is index 0 in every family
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
    """Unreached (representative, vertex) pairs over the 2k block representatives."""
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 6.0))
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

    # Exact constructions for small D.
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

    # Main search: bandit over base sizes k, each trial over a freshly sampled group.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        lo = best_n // (2 * k) + 1 + rng.randrange(0, 3)
        spec = _sample_group(lo, rng)
        if spec is None:
            continue
        G, M = _table(spec)
        if 2 * k * G <= best_n or G > _MAX_G:
            continue
        Ts, Invs = _ts_invs(G, M)
        trials[k] += 1
        slice_end = min(deadline, time.monotonic() + _SLICE)
        res = _search(d, D, k, G, Ts, Invs, rng, slice_end, _ITERS)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
