import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / small constructions.
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
# NEW PRIMARY METHOD: unstructured bipartite (d-regular) graphs grown and annealed.
#
# State: T[i, l] = B-side neighbour of A-vertex i in layer l. Every layer l is a
# permutation of range(h), so every vertex has degree exactly d.
#   * Growth adds one A and one B vertex by splitting one edge per layer
#     (keeps the layers permutations, so the graph stays d-regular).
#   * Annealing moves swap two targets inside one layer (keeps permutations).
#   * Cost = ordered pairs at distance > D (bit-packed reachability, numpy)
#            + PEN * (duplicate edges).
#   * Whenever cost reaches 0 the graph is a valid (d, D) graph; it becomes the
#     new incumbent and the next size is tried from it. Failed tries are discarded.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_PEN = 6


def _nbr_from_T(T, d):
    """Return nbr of shape (d, 2h): nbr[l, v] is the layer-l neighbour of vertex v (A = 0..h-1, B = h..2h-1)."""
    h = T.shape[0]
    nbr = np.empty((d, 2 * h), dtype=np.int64)
    nbr[:, :h] = (h + T).T
    Inv = np.empty((d, h), dtype=np.int64)
    cols = np.arange(h, dtype=np.int64)
    for l in range(d):
        Inv[l, T[:, l]] = cols
    nbr[:, h:] = Inv
    return nbr


def _reach_cost(nbr, n, D, R0):
    """Ordered pairs (u, v) with dist(u, v) > D, via packed bit reachability."""
    d = nbr.shape[0]
    R = R0
    for _ in range(D):
        new = R.copy()
        for l in range(d):
            new |= R[nbr[l]]
        if np.array_equal(new, R):
            break
        R = new
    return n * n - int(_POP8[R].sum())


def _dups(T):
    """Number of repeated targets within rows of T (i.e. duplicate edges)."""
    S = np.sort(T, axis=1)
    return int(np.count_nonzero(S[:, 1:] == S[:, :-1]))


def _swap(T, nbr, h, l, i1, i2):
    """Swap the B-targets of A-vertices i1, i2 in layer l. Calling twice restores the state."""
    j1 = T[i1, l]
    j2 = T[i2, l]
    T[i1, l] = j2
    T[i2, l] = j1
    nbr[l, i1] = h + j2
    nbr[l, i2] = h + j1
    nbr[l, h + j1] = i2
    nbr[l, h + j2] = i1


def _grow(T, d, rng):
    """Add one A-vertex and one B-vertex: in every layer split one edge (i, j) into (i, h) and (h, j)."""
    h = T.shape[0]
    new = np.empty((h + 1, d), dtype=np.int64)
    new[:h] = T
    rows = rng.sample(range(h), d)  # h >= d always
    for l, i in enumerate(rows):
        j = T[i, l]
        new[i, l] = h
        new[h, l] = j
    return new


def _anneal(T, d, D, R0, rng, deadline, temp0):
    """Anneal T until it is valid (returns T) or the deadline passes (returns None)."""
    h = T.shape[0]
    n = 2 * h
    nbr = _nbr_from_T(T, d)
    cur = _reach_cost(nbr, n, D, R0) + _PEN * _dups(T)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - start) / span
        temp = max(0.3, temp0 * (0.3 / temp0) ** frac)
        l = rng.randrange(d)
        i1, i2 = rng.sample(range(h), 2)
        _swap(T, nbr, h, l, i1, i2)
        new = _reach_cost(nbr, n, D, R0) + _PEN * _dups(T)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
        else:
            _swap(T, nbr, h, l, i1, i2)
    return T


def _grow_search(d, D, deadline, rng):
    """Grow and anneal a d-regular bipartite graph of diameter <= D. Returns the best valid T."""
    # Start: K_{d,d} as a cyclic Latin square (valid for any D >= 2).
    best = np.array([[(i + l) % d for l in range(d)] for i in range(d)], dtype=np.int64)
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.5:
            break
        tb = min(remaining, max(1.5, min(6.0, remaining)))
        h = best.shape[0] + 1
        cand = _grow(best, d, rng)
        R0 = np.packbits(np.eye(2 * h, dtype=bool), axis=1)
        res = _anneal(cand, d, D, R0, rng, now + tb, temp0=30.0)
        if res is not None:
            best = res
    return best


def _edges_from_T(T, d):
    h = T.shape[0]
    return [(i, h + int(T[i, l])) for i in range(h) for l in range(d)]


# ----------------------------------------------------------------------------
# Parent's fallback: bi-Cayley lifts over semidirect products Z_m x| Z_k2.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_SWAP_PROB = 0.3
_STRUCT_PROB = 0.5


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
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


def _structured_init(d, k, G, Ts, rng):
    """Geometric-progression start."""
    x = rng.randrange(1, G)
    powers = [0]
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
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _cost(k, G, D, nbr):
    """Unreached (representative, vertex) pairs over all 2k representatives."""
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


# ----------------------------------------------------------------------------
# Driver.
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

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions: return immediately (calibration-style cases).
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

    # Bold primary search: grow and anneal an unstructured d-regular bipartite graph.
    if d >= 3 and D >= 2:
        grow_deadline = start + 0.6 * budget
        T = _grow_search(d, D, grow_deadline, rng)
        if T.shape[0] > best_n // 2:
            consider(2 * T.shape[0], _edges_from_T(T, d))

    # Safety net: the bi-Cayley group search for the remaining time.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
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
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
