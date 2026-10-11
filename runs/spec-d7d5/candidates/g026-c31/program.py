import math
import random
import time

import numpy as np

import lib


_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


# ----------------------------------------------------------------------------
# Group multiplication tables. Elements are 0..G-1 and mul[x, y] = x*y.
# ----------------------------------------------------------------------------

def _semidirect_mul(m, k2, r):
    """Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e), element a*k2 + b."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    mul = ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    return G, mul


def _abelian_mul(a, b):
    """Z_a x Z_b, element i*b + j."""
    G = a * b
    x = np.arange(G, dtype=np.int64)
    i = x // b
    j = x % b
    mul = ((i[:, None] + i[None, :]) % a) * b + (j[:, None] + j[None, :]) % b
    return G, mul


def _sample_group(target, rng):
    """Return (G, mul) with |G| >= target, or None."""
    for _ in range(200):
        if rng.random() < 0.5:
            b = rng.choice([1, 2, 3, 4, 5, 6, 8, 10, 12])
            a = max(2, -(-target // b))
            return _abelian_mul(a, b)
        k2 = rng.choice([2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24])
        m = max(2, -(-target // k2))
        r = None
        for _ in range(80):
            c = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
        if r is None:
            continue
        return _semidirect_mul(m, k2, r)
    return None


def _tables(G, mul):
    """Ts[s, g] = g*s and Invs[s, h] = g with g*s = h."""
    Ts = np.ascontiguousarray(mul.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.arange(G, dtype=np.int64)[None, :]
    return Ts, Invs


# ----------------------------------------------------------------------------
# Bi-Cayley lift search. A-block i (vertices i*G+g) and B-block j (vertices
# (k+j)*G+h). Layer l pairs A_i with B_{layers[l][i]} via voltage s:
# A_{i,g} ~ B_{j, g*s}. Each layer is a bijection of blocks, so the graph is
# d-regular and bipartite whenever there are no duplicate (i, j, s) darts.
# ----------------------------------------------------------------------------

def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Per vertex, bit b set when representative block b is within distance D."""
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


def _cost(k, N, reach, dup):
    unreached = 2 * k * N - int(_POP[reach].sum())
    return unreached + _PENALTY * dup


def _dups(d, k, layers, S):
    keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
    return len(keys) - len(set(keys))


def _search(d, D, k, G, Ts, Invs, rng, deadline, steps, patience, sample):
    """Min-conflicts local search with sampled voltage moves. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    reach = _reach(k, G, D, nbr, d)
    cost = _cost(k, N, reach, _dups(d, k, layers, S))
    best_cost, last = cost, 0

    for t in range(steps):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last > patience:
            break

        # Layer-swap move (exchange B-targets of two A-blocks in one layer).
        if k >= 2 and rng.random() < 0.15:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _cost(k, N, r2, _dups(d, k, layers, S))
            if c2 <= cost or rng.random() < 0.03:
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        # Pick a dart touching a defective (representative, vertex) pair.
        bad = np.flatnonzero(reach != full)
        if bad.size and rng.random() < 0.8:
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

        # Evaluate sampled voltages for this dart, keep the best.
        old = S[l][i]
        bc, bs, br = None, None, None
        for _ in range(sample):
            s = rng.randrange(G)
            if s == old:
                continue
            S[l][i] = s
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], s)
            r2 = _reach(k, G, D, nbr, d)
            c2 = _cost(k, N, r2, _dups(d, k, layers, S))
            if bc is None or c2 < bc:
                bc, bs, br = c2, s, r2
        if bs is None:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)
            continue

        if bc <= cost or rng.random() < 0.03:
            S[l][i] = bs
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], bs)
            cost, reach = bc, br
            if cost < best_cost:
                best_cost, last = cost, t
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


# ----------------------------------------------------------------------------
# Exact baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_for(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle C_{2D}: bipartite, 2-regular, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best
        ar = _araujo_for(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Main search: bi-Cayley lifts over new group families and k in {1,2,3}.
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        target = base + 1 + rng.randrange(0, max(2, base // 20 + 2))
        g = _sample_group(target, rng)
        if g is None:
            continue
        G, mul = g
        if 2 * k * G <= best_n:
            continue
        Ts, Invs = _tables(G, mul)
        res = _search(d, D, k, G, Ts, Invs, rng, deadline,
                      steps=5000, patience=250, sample=24)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
