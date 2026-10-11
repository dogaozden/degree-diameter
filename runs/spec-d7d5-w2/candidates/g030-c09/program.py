import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline: projective-plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Finite groups as multiplication tables (M[x, y] = x*y, identity e).
# Used as the base group of a bi-Cayley lift. These are non-metabelian
# families, unlike the semidirect products used by the older search.
# ----------------------------------------------------------------------------

def _cyclic(n):
    x = np.arange(n, dtype=np.int64)
    return (x[:, None] + x[None, :]) % n, 0


def _direct(f1, f2):
    """Direct product of two (table, identity) pairs; index of (i, j) is i*G2 + j."""
    M1, e1 = f1
    M2, e2 = f2
    G1, G2 = M1.shape[0], M2.shape[0]
    M = (M1[:, None, :, None] * G2 + M2[None, :, None, :]).reshape(G1 * G2, G1 * G2)
    return M.astype(np.int64), e1 * G2 + e2


def _perm_group(n):
    """Symmetric group S_n as a multiplication table (n = 4 used here)."""
    gens = [tuple([1, 0] + list(range(2, n))), tuple(list(range(1, n)) + [0])]
    idt = tuple(range(n))
    elems = [idt]
    index = {idt: 0}
    frontier = [idt]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = tuple(x[g[i]] for i in range(n))
                if y not in index:
                    index[y] = len(elems)
                    elems.append(y)
                    new.append(y)
        frontier = new
    G = len(elems)
    M = np.empty((G, G), dtype=np.int64)
    for i, x in enumerate(elems):
        for j, y in enumerate(elems):
            M[i, j] = index[tuple(x[y[k]] for k in range(n))]
    return M, 0


def _psl2(p):
    """PSL(2, p) for prime p, elements are 2x2 matrices of det 1 modulo sign."""
    els = []
    for a, b, c, d in itertools.product(range(p), repeat=4):
        if (a * d - b * c) % p == 1:
            t = (a, b, c, d)
            nt = tuple((-x) % p for x in t)
            if t <= nt:
                els.append(t)
    A = np.array(els, dtype=np.int64)
    G = len(els)
    A0, A1, A2, A3 = A[:, 0], A[:, 1], A[:, 2], A[:, 3]

    def code(P0, P1, P2, P3):
        return ((P0 * p + P1) * p + P2) * p + P3

    lookup = np.full(p ** 4, -1, dtype=np.int64)
    lookup[code(A0, A1, A2, A3)] = np.arange(G)
    P0 = (A0[:, None] * A0[None, :] + A1[:, None] * A2[None, :]) % p
    P1 = (A0[:, None] * A1[None, :] + A1[:, None] * A3[None, :]) % p
    P2 = (A2[:, None] * A0[None, :] + A3[:, None] * A2[None, :]) % p
    P3 = (A2[:, None] * A1[None, :] + A3[:, None] * A3[None, :]) % p
    c1 = code(P0, P1, P2, P3)
    c2 = code((-P0) % p, (-P1) % p, (-P2) % p, (-P3) % p)
    M = lookup[np.minimum(c1, c2)]
    ec = min(code(1, 0, 0, 1), code(p - 1, 0, 0, p - 1))
    e = int(lookup[ec])
    return M.astype(np.int64), e


def _tables(M, e):
    """Ts[s, g] = g*s and Invs[s, h] = h*s^{-1}, the layout used by the lift search."""
    G = M.shape[0]
    inv = np.empty(G, dtype=np.int64)
    rows, cols = np.nonzero(M == e)
    inv[rows] = cols
    Ts = np.ascontiguousarray(M.T)
    Invs = np.ascontiguousarray(M[:, inv].T)
    return Ts, Invs


# ----------------------------------------------------------------------------
# Semidirect-product bi-Cayley family (fallback search).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                r = None
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


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
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


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
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
    """Annealing over voltages and layer permutations. Returns (n, edges) or None."""
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


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.88 * time_limit, time_limit - 6.0))
    deadline = start + budget
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

    try:
        # Stage 1: bi-Cayley lifts (k = 1) over non-semidirect finite groups.
        # A graph with 2|G| vertices needs |G| > best_n / 2.
        if d >= 3 and D >= 3:
            stage_end = start + 0.5 * budget
            makers = [
                lambda: _psl2(11),                                  # order 660
                lambda: _direct(_perm_group(4), _perm_group(4)),    # order 576
                lambda: _direct(_psl2(5), _cyclic(10)),             # order 600
                lambda: _direct(_psl2(7), _cyclic(4)),              # order 672
                lambda: _direct(_direct(_psl2(7), _cyclic(2)), _cyclic(2)),  # order 672
                lambda: _psl2(13),                                  # order 1092
            ]
            for idx, make in enumerate(makers):
                now = time.monotonic()
                if now >= stage_end:
                    break
                share_end = now + (stage_end - now) / (len(makers) - idx)
                M, e = make()
                G = M.shape[0]
                if 2 * G <= best_n or G < d:
                    continue
                Ts, Invs = _tables(M, e)
                while time.monotonic() < share_end:
                    res = _search(d, D, 1, G, Ts, Invs, rng, share_end, 6000)
                    if res is not None:
                        consider(res[0], res[1])
                        break

        # Stage 2: semidirect bi-Cayley lifts with k base vertices per side (fallback search).
        trials = {k: 0 for k in _KS}
        wins = {k: 0 for k in _KS}

        def pick_k():
            if rng.random() < 0.2:
                return rng.choice(_KS)
            return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

        search_deadline = start + 0.9 * budget
        while time.monotonic() < search_deadline:
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
            res = _search(d, D, k, G, Ts, Invs, rng, search_deadline, 4000)
            if res is not None:
                wins[k] += 1
                consider(res[0], res[1])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
