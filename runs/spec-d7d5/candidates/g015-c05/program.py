import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from the parent).
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
# Stage 1: bi-Cayley lifts over semidirect products (parent search, unchanged).
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
    """Uniform start."""
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


def _construct(d, D, deadline, rng):
    """Stage 1: exact constructions plus the lift search. Always returns a valid (n, edges)."""
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

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


# ----------------------------------------------------------------------------
# Stage 2 (new, high-risk): grow a valid graph by unstructured local search.
#
# Start from the stage-1 graph and repeatedly add a pair of new vertices (one
# per side). Vertices may have degree < d; only validity matters. Local moves:
#   add    : join two deficient vertices on opposite sides,
#   slide  : move one endpoint of an edge (x,y) to a deficient z on y's side,
#   switch : degree-preserving double edge swap between two side-0 vertices.
# The cost is the number of ordered unreached pairs, computed with bitsets
# in numpy. Annealing stops as soon as the cost is zero; the result is always
# re-checked with lib.is_valid.
# ----------------------------------------------------------------------------

def _two_color(n, adj):
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _sync(nb, nbr, v, pad):
    row = nb[v]
    k = len(row)
    nbr[v, :k] = row
    nbr[v, k:] = pad


def _bad_cost(N, nbr, d, D, Nmax, W):
    """Number of ordered pairs (u, v) of active vertices with dist > D (or unreachable)."""
    reach = np.zeros((Nmax + 1, W), dtype=np.uint64)
    idx = np.arange(N, dtype=np.int64)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for j in range(d):
            new[:Nmax] |= reach[nbr[:, j]]
        if np.array_equal(new, reach):
            break
        reach = new
    cnt = int(_POP[reach[:N].view(np.uint16)].sum())
    return N * N - cnt


def _anneal(N, nb, nbr, side, d, D, Nmax, W, rng, deadline, iters):
    """Anneal until the current graph on N vertices is valid. Returns True on success."""
    pad = Nmax

    def ap(op):
        kind, u, v = op
        if kind == 0:
            nb[u].append(v)
            nb[v].append(u)
        else:
            nb[u].remove(v)
            nb[v].remove(u)
        _sync(nb, nbr, u, pad)
        _sync(nb, nbr, v, pad)

    def inverse(op):
        kind, u, v = op
        return (1 - kind, u, v)

    cost = _bad_cost(N, nbr, d, D, Nmax, W)
    if cost == 0:
        return True
    c0 = float(cost)

    for t in range(iters):
        if time.monotonic() > deadline:
            return False
        def0 = [v for v in range(N) if len(nb[v]) < d and side[v] == 0]
        def1 = [v for v in range(N) if len(nb[v]) < d and side[v] == 1]
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        r = rng.random()
        if r < 0.3:
            if not def0 or not def1:
                continue
            u = rng.choice(def0)
            v = rng.choice(def1)
            if v in nb[u]:
                continue
            ops = [(0, u, v)]
        elif r < 0.6:
            x = rng.randrange(N)
            if not nb[x]:
                continue
            y = rng.choice(nb[x])
            cands = def1 if side[y] == 1 else def0
            if not cands:
                continue
            z = rng.choice(cands)
            if z == y or z in nb[x]:
                continue
            ops = [(1, x, y), (0, x, z)]
        else:
            S0 = [v for v in range(N) if side[v] == 0 and nb[v]]
            if len(S0) < 2:
                continue
            a = rng.choice(S0)
            b = rng.choice(nb[a])
            c = rng.choice(S0)
            e = rng.choice(nb[c])
            if a == c or b == e or e in nb[a] or b in nb[c]:
                continue
            ops = [(1, a, b), (1, c, e), (0, a, e), (0, c, b)]

        for op in ops:
            ap(op)
        new = _bad_cost(N, nbr, d, D, Nmax, W)
        if new == 0:
            return True
        if new <= cost or rng.random() < math.exp(-(new - cost) / temp):
            cost = new
        else:
            for op in reversed(ops):
                ap(inverse(op))
    return False


def _grow(d, D, n0, edges0, deadline, rng, moore):
    """Add vertex pairs one at a time while annealing succeeds. Returns (n, edges) or None."""
    if n0 + 2 > moore:
        return None
    Nmax = min(moore, n0 + max(8, n0 // 4))
    if Nmax < n0 + 2:
        return None
    adj = lib.adjacency(n0, edges0)
    col = _two_color(n0, adj)
    nb = [[] for _ in range(Nmax)]
    side = [0] * Nmax
    for v in range(n0):
        nb[v] = list(adj[v])
        side[v] = col[v]
    W = (Nmax + 63) // 64
    nbr = np.full((Nmax, d), Nmax, dtype=np.int64)
    for v in range(n0):
        _sync(nb, nbr, v, Nmax)

    best = None
    N = n0
    while time.monotonic() < deadline and N + 2 <= Nmax:
        side[N] = 0
        side[N + 1] = 1
        N += 2
        if not _anneal(N, nb, nbr, side, d, D, Nmax, W, rng, deadline, 20000):
            break
        edges = [(u, v) for u in range(N) for v in nb[u] if u < v]
        if not lib.is_valid(N, edges, d, D):
            break
        best = (N, edges)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Stage 1: structured constructions and lift search (safe, always valid).
    best = _construct(d, D, start + 0.35 * budget, rng)

    # Stage 2: unstructured growth from the stage-1 graph.
    moore = lib._moore_bound(d, D)
    if best[0] < moore and time.monotonic() < deadline:
        try:
            grown = _grow(d, D, best[0], best[1], deadline, rng, moore)
        except Exception:
            grown = None
        if grown is not None and grown[0] > best[0] and lib.is_valid(grown[0], grown[1], d, D):
            best = grown

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
