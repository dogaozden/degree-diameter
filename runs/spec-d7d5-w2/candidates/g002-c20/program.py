import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bipartite group lifts over semidirect products Z_m x| Z_k2, searched by
# simulated annealing. Compared with the parent, this variant:
#   * uses a wider family of base sizes a (up to 6 per side) and a wider set
#     of group shapes, sampled with a bandit over (a, k2);
#   * anneals at a cost that counts unreached (representative, vertex) pairs,
#     restarting from fresh structured or random starts when a run stalls;
#   * tries to grow the graph from the best valid order found so far.
# Every candidate is checked with lib.is_valid before it is kept, and the
# best valid graph found so far is always returned.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_AS = (1, 2, 3, 4, 5, 6)
_K2S = (1, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20, 24)
_SWAP_PROB = 0.3
_ITERS = 3000


def _sample_group(target, rng):
    """Return (m, k2, r) with Z_m x| Z_k2 of order m*k2 >= target, or None."""
    for _ in range(100):
        k2 = rng.choice(_K2S)
        m = max(2, -(-target // k2))
        if k2 == 1:
            return m, 1, 1
        r = None
        for _ in range(80):
            c = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
        if r is not None:
            return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs): Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h.

    Element (a, b) is coded a*k2 + b, with (a, b)(c, e) = (a + r^b c, b + e).
    Index 0 is the identity.
    """
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _structured_init(d, a, G, Ts, rng):
    """Geometric-progression start: layers[l][i] = (i + l) mod a, S[l][i] = y_i * x^(l+1)."""
    x = rng.randrange(1, G)
    powers = [0]
    for _ in range(d):
        powers.append(int(Ts[x, powers[-1]]))
    ys = [rng.randrange(G) for _ in range(a)]
    layers = [[(i + l) % a for i in range(a)] for l in range(d)]
    S = [[int(Ts[ys[i], powers[l + 1]]) for i in range(a)] for l in range(d)]
    return layers, S


def _random_init(d, a, G, rng):
    """Uniform start: a random permutation per layer and random voltages."""
    layers = [rng.sample(range(a), a) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(a)] for _ in range(d)]
    return layers, S


def _set_dart(nbr, a, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for A-vertex i (to B-vertex j, voltage s) and the matching B-side slots."""
    nbr[l, i * G:(i + 1) * G] = (a + j) * G + Ts[s]
    nbr[l, (a + j) * G:(a + j + 1) * G] = i * G + Invs[s]


def _cost(a, G, D, nbr):
    """Number of unreached (representative, vertex) pairs, over the 2a representatives."""
    d, N = nbr.shape
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * a):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return 2 * a * N - int(_POP[reach].sum())


def _search(d, D, a, G, Ts, Invs, rng, deadline, iters):
    """Annealing over voltages and per-layer target swaps. Returns (n, edges) or None."""
    N = 2 * a * G
    if rng.random() < 0.5:
        layers, S = _structured_init(d, a, G, Ts, rng)
    else:
        layers, S = _random_init(d, a, G, rng)
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(a):
            _set_dart(nbr, a, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(a)]
        return len(keys) - len(set(keys))

    cost = _cost(a, G, D, nbr) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)

        if a > 1 and rng.random() < _SWAP_PROB:
            i1, i2 = rng.sample(range(a), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, a, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, a, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            c2 = _cost(a, G, D, nbr) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, a, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, a, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        i = rng.randrange(a)
        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, a, G, Ts, Invs, l, i, layers[l][i], new)
        c2 = _cost(a, G, D, nbr) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[l][i] = old
            _set_dart(nbr, a, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(N):
        for v in nbr[:, u]:
            v = int(v)
            edges.add((min(u, v), max(u, v)))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Exact projective-plane incidence graph for D >= 3 (degree q+1 <= d).
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            pg = lib.projective_plane_incidence(q)
            consider(pg[0], pg[1])
            break
    if D == 3 and lib.is_prime_power(d - 1):
        return best

    # Main search: bandit over base sizes a and group shapes.
    trials = {a: 0 for a in _AS}
    wins = {a: 0 for a in _AS}

    def pick_a():
        if rng.random() < 0.2:
            return rng.choice(_AS)
        return max(_AS, key=lambda a: (wins[a] + 1) / (trials[a] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        a = pick_a()
        g_min = best_n // (2 * a) + 1
        target = g_min + rng.randrange(0, max(2, g_min // 16 + 1))
        grp = _sample_group(target, rng)
        if grp is None:
            continue
        m, k2, r = grp
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * a * G <= best_n:
            continue
        trials[a] += 1
        res = _search(d, D, a, G, Ts, Invs, rng, deadline, _ITERS)
        if res is not None:
            wins[a] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
