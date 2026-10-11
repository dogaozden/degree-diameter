import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact constructions (kept from the parent for the D = 3 and D = 4 cases).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph of degree d (q = d - 2 a prime power >= 3); diameter 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    return lib.araujo_lopez_graph(q)


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
# Bold change: bi-Cayley lifts over Frobenius groups AGL(1, q) (x -> a x + b),
# in addition to semidirect products Z_m x| Z_k2. The AGL(1, 25) group has
# order 600, so the k = 1 Haar-type lift has 1200 vertices, which beats the
# record of 1134 when it is valid.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l joins A_{i,g} to B_{perm[l][i], g*S[l][i]}. Each layer is a
# permutation, so every vertex has degree d. Left multiplication is an
# automorphism, so a diameter check needs only the 2k block representatives.
#
# Search: simulated annealing on the number of unreached (representative, vertex)
# pairs. Attempts are time-capped and use fresh random starts. Every result
# is checked with lib.is_valid. The fallback is K_{d,d}.
# ----------------------------------------------------------------------------

_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_MAX_G = 1300
_ITERS = 20000
_ATTEMPT_SECONDS = 6.0
_PEN = 1000


def _agl_M(q):
    """Multiplication table of AGL(1, q) with elements (a, b), a != 0, meaning x -> a x + b."""
    F = lib.GF(q)
    A = np.array([a for a in range(1, q) for _ in range(q)], dtype=np.int64)
    B = np.array([b for _ in range(1, q) for b in range(q)], dtype=np.int64)
    G = len(A)
    idx = np.full(q * q, -1, dtype=np.int64)
    idx[A * q + B] = np.arange(G)
    # (a1, b1) * (a2, b2) = (a1 a2, a1 b2 + b1)
    pa = F.mul_table[A[:, None], A[None, :]]
    pb = F.add_table[F.mul_table[A[:, None], B[None, :]], B[:, None]]
    M = idx[pa * q + pb]
    if (M < 0).any():
        raise ValueError("AGL table not closed")
    return G, M


def _semidirect_M(m, k2, r):
    """Multiplication table of Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b + e)."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    return G, M


def _tables(G, M):
    """Return (Ts, Invs, e): Ts[s, g] = g*s, Invs[s, h] = g with g*s = h, e = identity index."""
    x = np.arange(G, dtype=np.int64)
    e = int(np.nonzero(np.all(M == x[None, :], axis=1))[0][0])
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return Ts, Invs, e


def _agl_pick(need, cache):
    """Smallest AGL(1, q) (q prime power) with order q(q-1) >= need and order <= _MAX_G, prepared."""
    best_q = None
    for q in range(3, 40):
        if not lib.is_prime_power(q):
            continue
        order = q * (q - 1)
        if need <= order <= _MAX_G:
            if best_q is None or order < best_q * (best_q - 1):
                best_q = q
    if best_q is None:
        return None
    key = ("agl", best_q)
    if key not in cache:
        G, M = _agl_M(best_q)
        cache[key] = (G,) + _tables(G, M)
    return cache[key]


def _semi_pick(need, rng):
    """Random semidirect product Z_m x| Z_k2 with order in [need, _MAX_G], prepared."""
    for _ in range(100):
        k2 = rng.choice([1, 2, 3, 4, 6, 7, 8, 9, 12, 14, 16, 18, 21, 24, 28, 30, 36])
        target = need + rng.randrange(0, max(2, need // 6 + 1))
        m = max(2, -(-target // k2))
        if m * k2 > _MAX_G or m * k2 < need:
            continue
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
        G, M = _semidirect_M(m, k2, r)
        return (G,) + _tables(G, M)
    return None


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for A-block i (voltage s into B-block j) and the matching B-side rows."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _cost(k, G, D, e, nbr):
    """Unreached (representative, vertex) pairs over the 2k block representatives."""
    d, N = nbr.shape
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G + e] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return 2 * k * N - int(_POP[reach].sum())


def _anneal(d, D, k, G, Ts, Invs, e, rng, deadline, iters):
    """Simulated annealing over layer voltages and permutations. Returns (n, edges) or None."""
    N = 2 * k * G
    perm = [rng.sample(range(k), k) for _ in range(d)]
    if k == 1:
        S = [[s] for s in rng.sample(range(G), d)]
    else:
        S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, perm[l][i], S[l][i])

    def dupcount():
        seen = set()
        dup = 0
        for l in range(d):
            for i in range(k):
                key = (i, perm[l][i], S[l][i])
                if key in seen:
                    dup += 1
                seen.add(key)
        return dup

    cost = _cost(k, G, D, e, nbr) + _PEN * dupcount()
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = 0.2 + 2.0 * (1.0 - t / iters)
        l = rng.randrange(d)

        if k > 1 and rng.random() < 0.3:
            # Structural move: swap the B-targets of two A-blocks in layer l.
            i1, i2 = rng.sample(range(k), 2)
            p = perm[l]
            p[i1], p[i2] = p[i2], p[i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, p[i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, p[i2], S[l][i2])
            c2 = _cost(k, G, D, e, nbr) + _PEN * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                p[i1], p[i2] = p[i2], p[i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, p[i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, p[i2], S[l][i2])
            continue

        # Voltage move.
        i = rng.randrange(k)
        old = S[l][i]
        new = rng.randrange(G)
        if k == 1:
            used = {S[m][0] for m in range(d)}
            if new in used:
                continue
        elif new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, perm[l][i], new)
        c2 = _cost(k, G, D, e, nbr) + _PEN * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, perm[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 6.0))
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
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    if d == 2:
        # Cycle C_{2D}: optimal for degree 2.
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    # Exact constructions: return immediately when they are optimal.
    if D >= 3:
        try:
            pg = _best_pg(d)
        except Exception:
            pg = None
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

        if D == 3:
            try:
                aj = _araujo(d)
            except Exception:
                aj = None
            if aj is not None:
                consider(aj[0], aj[1])
                return best

    if D >= 4 and time.monotonic() < deadline:
        try:
            gq = _best_gq(d)
        except Exception:
            gq = None
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if D == 2:
        return best

    # Main search over bi-Cayley lifts.
    cache = {}
    while time.monotonic() < deadline:
        k = 1 if rng.random() < 0.7 else 2
        need = best_n // (2 * k) + 1
        prep = None
        if rng.random() < 0.6:
            try:
                prep = _agl_pick(need, cache)
            except Exception:
                prep = None
        if prep is None:
            try:
                prep = _semi_pick(need, rng)
            except Exception:
                prep = None
        if prep is None:
            continue
        G, Ts, Invs, e = prep
        if G < d or 2 * k * G <= best_n:
            continue
        attempt_deadline = min(deadline, time.monotonic() + _ATTEMPT_SECONDS)
        try:
            res = _anneal(d, D, k, G, Ts, Invs, e, rng, attempt_deadline, _ITERS)
        except Exception:
            res = None
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
