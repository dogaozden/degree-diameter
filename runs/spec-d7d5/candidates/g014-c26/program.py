import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Overview (new strategy for the target cases).
#
# Phase 1 (about 30% of the budget): bi-Cayley lifts over Z_m x| Z_k2, as in
#   the parent, to get a strong, d-regular bipartite starting graph.
# Phase 2 (the rest): a different method, vertex insertion plus switch repair.
#   * Grow: insert one A-vertex and one B-vertex into a d-regular bipartite
#     graph by taking a matching of d edges (a_i, b_i), deleting them, and
#     adding (x, b_i) and (a_i, y). The graph stays d-regular and bipartite.
#   * Repair: simulated annealing with 2-switches on the edge set. A switch
#     replaces (a1,b1),(a2,b2) by (a1,b2),(a2,b1), which preserves degrees.
#     The cost is the number of ordered pairs at distance > D, computed with
#     bit-packed reachability sets in numpy.
# Every returned graph passes lib.is_valid. Fallbacks are K_{d,d}, the cycle
# for d = 2, and the exact PG(2,q) incidence graph for D = 3.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_PENALTY = 1000
_KS = (1, 2, 3, 4)
_SWAP_PROB = 0.3
_STRUCT_PROB = 0.5
_ITERS = 4000


# ------------------------------- phase 1: bi-Cayley lifts ---------------------

def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            return m, 1, 1
        for _ in range(60):
            c = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                return m, k2, c
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs): Ts[s, g] = g*s and Invs[s, h] = g with g*s = h, in Z_m x| Z_k2."""
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
    x = rng.randrange(1, G)
    powers = [0]
    for _ in range(d):
        powers.append(int(Ts[x, powers[-1]]))
    ys = [rng.randrange(G) for _ in range(k)]
    layers = [[(i + l) % k for i in range(k)] for l in range(d)]
    S = [[int(Ts[ys[i], powers[l + 1]]) for i in range(k)] for l in range(d)]
    return layers, S


def _random_init(d, k, G, rng):
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    return layers, S


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _lift_cost(k, G, D, nbr):
    """Unreached (representative, vertex) pairs over the 2k block representatives."""
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
    pop = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
    return 2 * k * N - int(pop[reach].sum())


def _lift_search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    """Annealing over voltages and per-layer target swaps. Returns (N, edges) or None."""
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

    cost = _lift_cost(k, G, D, nbr) + _PENALTY * dupcount()
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
            c2 = _lift_cost(k, G, D, nbr) + _PENALTY * dupcount()
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
        c2 = _lift_cost(k, G, D, nbr) + _PENALTY * dupcount()
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


# ------------------------------- phase 2: insertion + switch repair -----------

def _bad_pairs(N, nbr, D):
    """Ordered pairs (u, v) with distance > D, for a d-regular graph given as an (N, d) table."""
    d = nbr.shape[1]
    W = (N + 7) // 8
    idx = np.arange(N)
    reach = np.zeros((N, W), dtype=np.uint8)
    reach[idx, idx >> 3] = np.left_shift(1, idx & 7).astype(np.uint8)
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[:, l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return N * N - int(_POP8[reach].sum())


def _nbr(ANB, BNB, s):
    """Full neighbour table: A vertices 0..s-1, B vertices s..2s-1."""
    return np.vstack([ANB + s, BNB])


def _switch(ANB, BNB, adjA, a1, s1, a2, s2):
    """Replace (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Returns an undo record or None if illegal."""
    b1 = int(ANB[a1, s1])
    b2 = int(ANB[a2, s2])
    if a1 == a2 or b1 == b2 or b2 in adjA[a1] or b1 in adjA[a2]:
        return None
    j1 = int(np.flatnonzero(BNB[b1] == a1)[0])
    j2 = int(np.flatnonzero(BNB[b2] == a2)[0])
    ANB[a1, s1] = b2
    ANB[a2, s2] = b1
    BNB[b1, j1] = a2
    BNB[b2, j2] = a1
    adjA[a1].discard(b1)
    adjA[a1].add(b2)
    adjA[a2].discard(b2)
    adjA[a2].add(b1)
    return (a1, s1, b1, a2, s2, b2, j1, j2)


def _undo(ANB, BNB, adjA, u):
    a1, s1, b1, a2, s2, b2, j1, j2 = u
    ANB[a1, s1] = b1
    ANB[a2, s2] = b2
    BNB[b1, j1] = a1
    BNB[b2, j2] = a2
    adjA[a1].discard(b2)
    adjA[a1].add(b1)
    adjA[a2].discard(b1)
    adjA[a2].add(b2)


def _grow(ANB, BNB, d, rng):
    """Insert one A and one B vertex into a d-regular bipartite graph, keeping it d-regular."""
    s = ANB.shape[0]
    ANB2 = np.vstack([ANB, np.zeros((1, d), dtype=np.int64)])
    BNB2 = np.vstack([BNB, np.zeros((1, d), dtype=np.int64)])
    x, y = s, s
    used_a, used_b = set(), set()
    pairs = []
    order = list(range(s))
    rng.shuffle(order)
    for a in order:
        if len(pairs) == d:
            break
        slot = rng.randrange(d)
        b = int(ANB[a, slot])
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        pairs.append((a, slot, b))
    if len(pairs) < d:
        return None
    for l, (a, slot, b) in enumerate(pairs):
        j = int(np.flatnonzero(BNB[b] == a)[0])
        ANB2[a, slot] = y
        BNB2[b, j] = x
        ANB2[x, l] = b
        BNB2[y, l] = a
    return ANB2, BNB2


def _anneal(ANB, BNB, d, D, rng, deadline):
    """Repair by 2-switches until the diameter is at most D. Returns (ANB, BNB) or None."""
    s = ANB.shape[0]
    N = 2 * s
    ANB = ANB.copy()
    BNB = BNB.copy()
    adjA = [set(r) for r in ANB.tolist()]
    cost = _bad_pairs(N, _nbr(ANB, BNB, s), D)
    while cost > 0 and time.monotonic() < deadline:
        a1 = rng.randrange(s)
        s1 = rng.randrange(d)
        a2 = rng.randrange(s)
        s2 = rng.randrange(d)
        u = _switch(ANB, BNB, adjA, a1, s1, a2, s2)
        if u is None:
            continue
        nc = _bad_pairs(N, _nbr(ANB, BNB, s), D)
        temp = 0.5 + 0.01 * cost
        if nc <= cost or rng.random() < math.exp(-(nc - cost) / temp):
            cost = nc
        else:
            _undo(ANB, BNB, adjA, u)
    if cost == 0:
        return ANB, BNB
    return None


def _to_state(n, edges, d):
    """Convert a d-regular bipartite graph (A = first half, B = second half) to (ANB, BNB)."""
    s = n // 2
    ANB = [[] for _ in range(s)]
    BNB = [[] for _ in range(s)]
    for u, v in edges:
        if u > v:
            u, v = v, u
        if u >= s or v < s:
            return None
        ANB[u].append(v - s)
        BNB[v - s].append(u)
    if any(len(r) != d for r in ANB) or any(len(r) != d for r in BNB):
        return None
    return np.array(ANB, dtype=np.int64), np.array(BNB, dtype=np.int64)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(0.5, min(0.9 * time_limit, time_limit - 5.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, which has diameter 2 and is Moore-optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best

    # ---- phase 1: bi-Cayley lifts (about 30% of the budget) ----
    lift_deadline = t0 + 0.3 * budget
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < lift_deadline:
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
        res = _lift_search(d, D, k, G, Ts, Invs, rng, lift_deadline, _ITERS)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # ---- phase 2: grow by insertion, repair by switches ----
    state = None
    if best_n > 2 * d:
        state = _to_state(best_n, best[1], d)
    if state is None:
        K = np.tile(np.arange(d, dtype=np.int64), (d, 1))
        state = (K, K.copy())
    ANB, BNB = state

    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.3:
            break
        grown = _grow(ANB, BNB, d, rng)
        if grown is None:
            break
        A2, B2 = grown
        span = max(1.0, 0.5 * remaining)
        res = _anneal(A2, B2, d, D, rng, min(deadline, now + span))
        if res is not None:
            ANB, BNB = res
            s = ANB.shape[0]
            edges = [(a, s + int(b)) for a in range(s) for b in ANB[a].tolist()]
            consider(2 * s, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
