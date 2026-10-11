import itertools
import math
import random
import time

import numpy as np

import lib


_PEN = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_K2 = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 28, 30, 36]


# ----------------------------------------------------------------------------
# Safe baseline: projective plane incidence graph (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group catalogue. Each group is given by its multiplication table M (G x G),
# with the identity at index 0. Bi-Cayley graphs over any such group are
# vertex-transitive within each block (left multiplication is an automorphism),
# so the diameter check only needs one representative per block.
# ----------------------------------------------------------------------------

def _semidirect_mul(m, k2, r):
    """Multiplication table of Z_m x| Z_k2, element (a, b) coded as a*k2 + b."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    return ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2


def _agl_mul(q):
    """Affine group AGL(1, q): maps x -> a x + b, a != 0; code (a, b) as (a-1)*q + b."""
    F = lib.GF(q)
    T, A = F.mul_table, F.add_table
    a = np.repeat(np.arange(1, q, dtype=np.int64), q)
    b = np.tile(np.arange(q, dtype=np.int64), q - 1)
    na = T[a[:, None], a[None, :]]
    nb = A[T[a[:, None], b[None, :]], b[:, None]]
    return (na - 1) * q + nb


def _pgl_mul(q):
    """Projective general linear group PGL(2, q) on normalized 2x2 matrices, identity first."""
    F = lib.GF(q)
    T, A = F.mul_table, F.add_table
    els = [(1, 0, 0, 1)]
    for t in itertools.product(range(q), repeat=4):
        if not any(t) or t == (1, 0, 0, 1):
            continue
        if next(x for x in t if x) != 1:
            continue
        det = F.sub(F.mul(t[0], t[3]), F.mul(t[1], t[2]))
        if det:
            els.append(t)
    E = np.array(els, dtype=np.int64)
    G = len(els)
    a1, b1, c1, d1 = (E[:, i][:, None] for i in range(4))
    a2, b2, c2, d2 = (E[:, i][None, :] for i in range(4))
    P0 = A[T[a1, a2], T[b1, c2]]
    P1 = A[T[a1, b2], T[b1, d2]]
    P2 = A[T[c1, a2], T[d1, c2]]
    P3 = A[T[c1, b2], T[d1, d2]]
    P = np.stack([P0, P1, P2, P3], axis=2)
    first = np.argmax(P != 0, axis=2)
    lead = np.take_along_axis(P, first[:, :, None], axis=2)[:, :, 0]
    inv = np.array([0] + [F.inv(x) for x in range(1, q)], dtype=np.int64)
    scale = inv[lead]
    Pn = T[scale[:, :, None], P]
    code = ((Pn[..., 0] * q + Pn[..., 1]) * q + Pn[..., 2]) * q + Pn[..., 3]
    lut = np.full(q ** 4, -1, dtype=np.int64)
    ecode = ((E[:, 0] * q + E[:, 1]) * q + E[:, 2]) * q + E[:, 3]
    lut[ecode] = np.arange(G)
    M = lut[code]
    if (M < 0).any():
        raise AssertionError("PGL table construction failed")
    return M


def _catalog():
    """Fixed groups as (order, (kind, parameter))."""
    cat = []
    for q in range(5, 41):
        if lib.is_prime_power(q):
            cat.append((q * (q - 1), ("agl", q)))
    for q in (7, 8, 9):
        cat.append((q * (q * q - 1), ("pgl", q)))
    return cat


def _sample_semidirect(lo, hi, rng):
    """Random Z_m x| Z_k2 with order in [lo, hi], or None."""
    for _ in range(100):
        k2 = rng.choice(_K2)
        mlo = -(-lo // k2)
        mhi = hi // k2
        if mlo > mhi or mhi < 2:
            continue
        m = rng.randint(max(2, mlo), mhi)
        if k2 == 1:
            r = 1
        else:
            if m < 3:
                continue
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


def _tables(M):
    """Right-multiplication table Ts[s, x] = x*s and its inverse Invs[s, y] = y*s^{-1}."""
    G = M.shape[0]
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(np.arange(G, dtype=np.int64)[None, :], (G, G))
    return Ts, Invs


# ----------------------------------------------------------------------------
# Bi-Cayley lifts: k base vertices per side, d layers. Layer l matches A-block i
# to B-block layers[l][i] with voltage S[l][i]. Each layer is a perfect matching
# of blocks, so the graph is d-regular and bipartite.
# ----------------------------------------------------------------------------

def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Per-vertex bitmask of block representatives within distance D."""
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


def _anneal(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing over layers and voltages. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dup():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    def score():
        r = _reach(k, G, D, nbr, d)
        return r, _unreached(k, N, r) + _PEN * dup()

    reach, cost = score()
    c0 = float(max(cost, 1))
    best_cost = cost
    last = 0
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline or t - last > patience:
            break
        temp = max(0.3, 0.02 * c0 * (1.0 - t / iters))

        if k >= 2 and rng.random() < 0.2:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2, c2 = score()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
        else:
            bad = np.flatnonzero(reach != full) if rng.random() < 0.5 else None
            if bad is not None and bad.size:
                u = int(bad[rng.randrange(bad.size)])
                blk = u // G
                l = rng.randrange(d)
                if blk < k:
                    i = blk
                else:
                    i = layers[l].index(blk - k)
            else:
                l = rng.randrange(d)
                i = rng.randrange(k)
            old = S[l][i]
            new = rng.randrange(G)
            if new == old:
                continue
            S[l][i] = new
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
            r2, c2 = score()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                S[l][i] = old
                _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

        if cost < best_cost:
            best_cost, last = cost, t

    if cost != 0:
        return None
    edges = []
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.append((u, int(v)))
    return N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, time_limit - 9.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
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

    # Goal for the target case; after 60% of the budget, accept a lower floor
    # so that a safe, non-trivial result is still produced.
    goal = 1142 if (d, D) == (7, 5) else 0
    switch = start + 0.6 * max(1.0, deadline - start)

    cat = _catalog()
    try:
        while time.monotonic() < deadline:
            now = time.monotonic()
            floor_n = goal if (goal == 0 or now < switch) else 1000
            need = max(best_n + 1, floor_n)
            k = rng.choices([1, 2, 3, 4], weights=[5, 3, 2, 1])[0]
            lo = -(-need // (2 * k))
            hi = int(lo * 1.25) + 2

            cands = [e for e in cat if lo <= e[0] <= hi]
            if cands and rng.random() < 0.5:
                _, (kind, q) = rng.choice(cands)
                M = _agl_mul(q) if kind == "agl" else _pgl_mul(q)
            else:
                g = _sample_semidirect(lo, hi, rng)
                if g is None:
                    continue
                M = _semidirect_mul(*g)

            G = M.shape[0]
            if 2 * k * G <= best_n:
                continue
            Ts, Invs = _tables(M)
            res = _anneal(d, D, k, G, Ts, Invs, rng, deadline, 40000, 3000)
            if res is not None:
                consider(res[0], res[1])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
