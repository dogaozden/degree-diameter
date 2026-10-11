import math
import random
import time

import numpy as np

import lib


_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_KW = (4, 3, 2, 1)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group families. Each spec yields a multiplication table M with M[x, y] = x*y.
# ----------------------------------------------------------------------------

def _sample_spec(lo, hi, rng):
    """Return a group spec whose order lies in [lo, hi], or None."""
    for _ in range(300):
        t = rng.random()
        if t < 0.25:
            m = rng.randint(lo, hi)
            return ("c", m)
        if t < 0.40:
            a = (lo + 1) // 2
            b = hi // 2
            if a > b or b < 2:
                continue
            return ("d", rng.randint(max(2, a), b))
        if t < 0.60:
            n = rng.randint(2, 12)
            a = -(-lo // n)
            b = hi // n
            if a > b or b < 2:
                continue
            return ("p", rng.randint(max(2, a), b), n)
        k2 = rng.choice([2, 3, 4, 5, 6, 7, 8, 9, 10, 12])
        a = -(-lo // k2)
        b = hi // k2
        if a > b or b < 2:
            continue
        m = rng.randint(max(2, a), b)
        r = 1
        for _ in range(60):
            if m <= 2:
                break
            c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
        return ("s", m, k2, r)
    return None


def _tables(spec):
    """Return (G, Ts, Invs): Ts[s, g] = g*s and Invs[s, h] = g with g*s = h."""
    t = spec[0]
    if t == "c":
        m = spec[1]
        G = m
        x = np.arange(m, dtype=np.int64)
        M = (x[:, None] + x[None, :]) % m
    elif t == "d":
        m = spec[1]
        G = 2 * m
        x = np.arange(G, dtype=np.int64)
        a = x // 2
        b = x % 2
        sign = np.where(b == 0, 1, -1).astype(np.int64)
        A = (a[:, None] + sign[:, None] * a[None, :]) % m
        B = (b[:, None] + b[None, :]) % 2
        M = A * 2 + B
    elif t == "p":
        m, n = spec[1], spec[2]
        G = m * n
        x = np.arange(G, dtype=np.int64)
        a = x // n
        b = x % n
        M = ((a[:, None] + a[None, :]) % m) * n + (b[:, None] + b[None, :]) % n
    else:
        m, k2, r = spec[1], spec[2], spec[3]
        G = m * k2
        x = np.arange(G, dtype=np.int64)
        a = x // k2
        b = x % k2
        powers = np.array([pow(r, e, m) for e in range(k2)], dtype=np.int64)
        M = ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    x = np.arange(G, dtype=np.int64)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


# ----------------------------------------------------------------------------
# Bi-Cayley lifts. A_{i,g} = i*G + g, B_{j,h} = (k+j)*G + h.
# Layer l pairs A-block i with B-block layers[l][i] via voltage S[l][i]:
# A_{i,g} ~ B_{j,g*s}. Each layer is a permutation, so every vertex has degree d.
# ----------------------------------------------------------------------------

def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex of which block representatives lie within distance D."""
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


def _sa(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing on unreached pairs plus duplicate penalty. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dups():
        seen = set()
        c = 0
        for l in range(d):
            for i in range(k):
                key = (i, layers[l][i], S[l][i])
                if key in seen:
                    c += 1
                else:
                    seen.add(key)
        return c

    def evaluate():
        r = _reach(k, G, D, nbr, d)
        unr = 2 * k * N - int(_POP[r].sum())
        return unr + _PENALTY * dups()

    cost = evaluate()
    c0 = float(max(cost, 1))
    best = cost
    last = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline or t - last > patience:
            break
        temp = max(0.5, 0.02 * c0 * (1.0 - t / iters))

        if k >= 2 and rng.random() < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            c2 = evaluate()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
                if cost < best:
                    best, last = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        l = rng.randrange(d)
        i = rng.randrange(k)
        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        c2 = evaluate()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            if cost < best:
                best, last = cost, t
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

    # Safe fallback: K_{d,d} has diameter 2.
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

    if D == 2:
        return best

    try:
        fails = 0
        while time.monotonic() < deadline:
            k = rng.choices(_KS, weights=_KW)[0]
            lo = best_n // (2 * k) + 1
            spread = max(2, lo // 40) * (1 + fails // 5)
            hi = lo + spread
            spec = _sample_spec(lo, hi, rng)
            if spec is None:
                fails += 1
                continue
            G, Ts, Invs = _tables(spec)
            if 2 * k * G <= best_n:
                fails += 1
                continue
            res = _sa(d, D, k, G, Ts, Invs, rng, deadline, 3000, 900)
            if res is not None:
                fails = 0
                consider(res[0], res[1])
            else:
                fails += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
