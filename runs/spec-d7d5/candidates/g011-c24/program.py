import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (simulated annealing).
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
    """Geometric-progression start: layers[l][i] = (i + l) mod k, S[l][i] = y_i * x^(l+1)."""
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
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
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
# NEW: packed-bitset distance counter and degree-preserving edge-switch growth.
#
# _bad_pairs counts unordered pairs at distance > D (unreachable pairs count),
# using bit-packed reach sets in numpy: each vertex's ball is a row of uint64
# words. It is far faster than lib.within_diameter for repeated checks.
#
# Growth: insert a pair (x, y) by removing a matching of d-1 edges and wiring
# x to their B ends, y to their A ends, and x-y. Degrees are preserved. The
# resulting defect is then repaired by random double-edge switches (a1b1, a2b2
# -> a1b2, a2b1), which keep every degree and the bipartition. Annealing on
# the bad-pair count tries to reach zero within a few dozen switches. A failed
# attempt is discarded, so the current graph is always valid.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)
_GROW_STEPS = 80
_GROW_T = 0.7


def _bad_pairs(n, nb, D):
    """Unordered pairs at distance > D. nb is an (n, dm) neighbour table padded with the vertex itself."""
    W = (n + 63) // 64
    idx = np.arange(n, dtype=np.int64)
    reach = np.zeros((n, W), dtype=np.uint64)
    reach[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(D):
        new = reach | np.bitwise_or.reduce(reach[nb], axis=1)
        if np.array_equal(new, reach):
            break
        reach = new
    total = int(_POP8[reach.view(np.uint8)].sum())
    return (n * n - total) // 2


def _nbr_table(n, A, B):
    """Build the padded neighbour table for edges (A[i], B[i])."""
    adj = [[] for _ in range(n)]
    for a, b in zip(A, B):
        adj[a].append(b)
        adj[b].append(a)
    dm = max(1, max(len(x) for x in adj))
    nb = np.empty((n, dm), dtype=np.int64)
    for v in range(n):
        row = adj[v]
        nb[v, :len(row)] = row
        nb[v, len(row):] = v
    return nb


def _repl(nb, row, old, new):
    """In row `row` of nb, replace the entry `old` by `new`."""
    k = int(np.argmax(nb[row] == old))
    nb[row, k] = new


def _switch(i, j, A, B, S, nb):
    """Degree-preserving switch of edges i=(a1,b1), j=(a2,b2) into (a1,b2), (a2,b1). Self-inverse."""
    a1, b1, a2, b2 = A[i], B[i], A[j], B[j]
    if (a1, b2) in S or (a2, b1) in S:
        return False
    S.discard((a1, b1))
    S.discard((a2, b2))
    S.add((a1, b2))
    S.add((a2, b1))
    B[i] = b2
    B[j] = b1
    _repl(nb, a1, b1, b2)
    _repl(nb, b1, a1, a2)
    _repl(nb, a2, b2, b1)
    _repl(nb, b2, a2, a1)
    return True


def _insert_pair(n, A, B, d, rng):
    """Remove a random matching of up to d-1 edges and add a new A-vertex x and B-vertex y joined to each other."""
    m = len(A)
    order = list(range(m))
    rng.shuffle(order)
    usedA, usedB, chosen = set(), set(), []
    for idx in order:
        if len(chosen) >= d - 1:
            break
        a, b = A[idx], B[idx]
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        chosen.append(idx)
    if not chosen:
        return None
    drop = set(chosen)
    nA = [A[i] for i in range(m) if i not in drop]
    nB = [B[i] for i in range(m) if i not in drop]
    x, y = n, n + 1
    for idx in chosen:
        nA.append(x)
        nB.append(B[idx])
        nA.append(A[idx])
        nB.append(y)
    nA.append(x)
    nB.append(y)
    return n + 2, nA, nB


def _grow_attempt(n, A, B, d, D, rng):
    """Insert a vertex pair and anneal with switches until valid. Returns (n, A, B) or None."""
    res = _insert_pair(n, A, B, d, rng)
    if res is None:
        return None
    n2, A2, B2 = res
    m = len(A2)
    if m < 2:
        return None
    S = set(zip(A2, B2))
    nb = _nbr_table(n2, A2, B2)
    cost = _bad_pairs(n2, nb, D)
    steps = 0
    while cost > 0 and steps < _GROW_STEPS:
        steps += 1
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j or not _switch(i, j, A2, B2, S, nb):
            continue
        c2 = _bad_pairs(n2, nb, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / _GROW_T):
            cost = c2
        else:
            _switch(i, j, A2, B2, S, nb)  # undo
    if cost == 0:
        return n2, A2, B2
    return None


def _colours(n, edges):
    """Proper 2-colouring of a bipartite graph (BFS); returns a list of 0/1 per vertex."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if col[w] == -1:
                    col[w] = 1 - col[u]
                    stack.append(w)
    return col


def _grow_switch(n, edges, d, D, rng, deadline):
    """Repeatedly grow by a vertex pair with switch repair. Returns (n, A, B) of the final valid graph."""
    col = _colours(n, edges)
    A, B = [], []
    for u, v in edges:
        if col[u] == 0:
            A.append(int(u))
            B.append(int(v))
        else:
            A.append(int(v))
            B.append(int(u))
    while time.monotonic() < deadline:
        res = _grow_attempt(n, A, B, d, D, rng)
        if res is not None:
            n, A, B = res
    return n, list(zip(A, B))


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    search_deadline = start + 0.4 * budget
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

    if D >= 4 and time.monotonic() < search_deadline:
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

    # Growth phase: switch-repaired vertex-pair insertion on the best graph.
    if d >= 3 and time.monotonic() < deadline:
        gn, ge = _grow_switch(best[0], list(best[1]), d, D, rng, deadline)
        consider(gn, ge)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
