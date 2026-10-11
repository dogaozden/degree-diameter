import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Island focus: d=7, D=5. Bold change: replace the annealed bi-Cayley search
# with an exhaustive coordinate line search over semidirect-product voltages.
#
# Model: a bi-Cayley lift over G = Z_m x| Z_k2 with k A-blocks and k B-blocks.
# Layer l is a perfect matching of A-blocks to B-blocks (a permutation), and
# dart (l, i) carries a voltage s in G, giving vertex (i, x) ~ (k+j, x*s).
# Left multiplication by G is an automorphism, so the diameter condition reduces
# to: every vertex is within distance D of each of the 2k block representatives.
#
# Search: pick a coordinate (layer, block) and evaluate many candidate voltages
# exactly, keeping the best (monotone descent). Plateau moves are accepted, and
# stagnation triggers a perturbation of the best state. Layer swaps are also
# tried. Each success is verified by lib.is_valid before it is accepted.
# Fallbacks (PG incidence, K_{d,d}) are always valid, so every case returns.
# ----------------------------------------------------------------------------

_PEN = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_NCAND = 80
_ATT = 10.0


def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) with G = m*k2 >= target for Z_m x| Z_k2, or None."""
    opts = [1, 1, 1, 2, 2, 3, 4, 5, 6, 7, 8]
    for _ in range(100):
        k2 = rng.choice(opts)
        m = max(2, -(-target // k2))
        if k2 == 1:
            return m, 1, 1
        for _ in range(80):
            r = rng.randrange(1, m)
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                return m, k2, r
    return None


def _tables(m, k2, r):
    """Return (Ts, Invs): Ts[s][x] = x*s and Invs[s][y] = y*s^-1 in Z_m x| Z_k2."""
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
    return Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's darts for A-block i (to B-block j with voltage s)."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _fill(nbr, k, G, Ts, Invs, d, layers, S):
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])


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


def _cost(k, G, D, nbr, d, layers, S):
    """Unreached (vertex, representative) pairs plus penalty for duplicate darts."""
    N = 2 * k * G
    reach = _reach(k, G, D, nbr, d)
    unreached = 2 * k * N - int(_POP[reach].sum())
    keys = set()
    dup = 0
    for l in range(d):
        for i in range(k):
            key = (i, layers[l][i], S[l][i])
            if key in keys:
                dup += 1
            else:
                keys.add(key)
    return unreached + _PEN * dup, reach


def _search(d, D, k, G, Ts, Invs, rng, deadline):
    """Coordinate descent with exhaustive voltage line search. Returns (N, edges) or None."""
    N = 2 * k * G
    nb = np.empty((d, N), dtype=np.int64)
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    _fill(nb, k, G, Ts, Invs, d, layers, S)
    cost, _ = _cost(k, G, D, nb, d, layers, S)
    best_cost = cost
    best_layers = [row[:] for row in layers]
    best_S = [row[:] for row in S]
    stall = 0

    while cost > 0:
        if time.monotonic() > deadline:
            break
        if stall > 300:
            # Perturb from the best state.
            layers = [row[:] for row in best_layers]
            S = [row[:] for row in best_S]
            for _ in range(3):
                l = rng.randrange(d)
                i = rng.randrange(k)
                S[l][i] = rng.randrange(G)
            _fill(nb, k, G, Ts, Invs, d, layers, S)
            cost, _ = _cost(k, G, D, nb, d, layers, S)
            stall = 0
            continue

        if k >= 2 and rng.random() < 0.15:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nb, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nb, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            c, _ = _cost(k, G, D, nb, d, layers, S)
            if c <= cost:
                cost = c
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nb, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nb, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)
            old = S[l][i]
            cands = rng.sample(range(G), min(G, _NCAND))
            if old not in cands:
                cands.append(old)
            bestc = None
            bests = old
            for s in cands:
                S[l][i] = s
                _set_dart(nb, k, G, Ts, Invs, l, i, layers[l][i], s)
                c, _ = _cost(k, G, D, nb, d, layers, S)
                if bestc is None or c < bestc:
                    bestc, bests = c, s
            S[l][i] = bests
            _set_dart(nb, k, G, Ts, Invs, l, i, layers[l][i], bests)
            cost = bestc

        if cost < best_cost:
            best_cost = cost
            best_layers = [row[:] for row in layers]
            best_S = [row[:] for row in S]
            stall = 0
        else:
            stall += 1

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nb[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.82 * time_limit, time_limit - 8.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])

    KS = [1, 2, 3, 4, 5]
    while time.monotonic() < deadline - 1.0:
        remaining = deadline - time.monotonic()
        att = min(_ATT, max(3.0, remaining / 3.0))
        k = rng.choice(KS)
        Gt = best[0] // (2 * k) + 1 + rng.randrange(0, 3)
        g = _sample_group(Gt, rng)
        if g is None:
            continue
        m, k2, r = g
        G = m * k2
        if 2 * k * G <= best[0]:
            continue
        try:
            Ts, Invs = _tables(m, k2, r)
            res = _search(d, D, k, G, Ts, Invs, rng,
                          min(deadline, time.monotonic() + att))
        except Exception:
            res = None
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
