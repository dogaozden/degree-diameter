import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline family: incidence graph of a projective plane.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (simulated annealing).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_SWAP_PROB = 0.3
_STRUCT_PROB = 0.5
_ANNEAL_ITERS = 2500


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
# NEW: degree-preserving double-edge-swap annealing repair on bipartite graphs.
#
# Given a bipartite graph whose vertices are A (colour 0) and B (colour 1),
# and a 'pair insertion' that adds two new vertices x (A) and y (B) by
# detaching a matching of d-1 edges, the result usually has a few bad pairs.
# We repair it with random double-edge swaps (a1,b1),(a2,b2) -> (a1,b2),(a2,b1),
# which keep every degree and the bipartition, and accept by Metropolis on the
# number of unreached vertex pairs. The reachability cost is computed with
# packed uint8 bitsets in numpy.
# ----------------------------------------------------------------------------

def _colours(n, edges):
    """Proper 2-colouring of a bipartite graph (DFS); returns a list of 0/1 per vertex."""
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


def _orient(n, edges):
    """Return edges as (A, B) pairs with A of colour 0."""
    col = _colours(n, edges)
    return [(u, v) if col[u] == 0 else (v, u) for u, v in edges]


def _unreached_pairs(nbr, N, D):
    """Number of unordered vertex pairs at distance > D, via packed bitsets. nbr has shape (d, N)."""
    W = (N + 7) // 8
    idx = np.arange(N)
    reach = np.zeros((N, W), dtype=np.uint8)
    reach[idx, idx >> 3] = (1 << (idx & 7)).astype(np.uint8)
    for _ in range(D):
        new = reach.copy()
        for l in range(nbr.shape[0]):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    pop = int(_POP8[reach].sum())
    return (N * N - pop) // 2


def _replace(nbr, v, old, new):
    """In row slot of vertex v, replace neighbour old by new (old must be present exactly once)."""
    l = int(np.flatnonzero(nbr[:, v] == old)[0])
    nbr[l, v] = new


def _anneal(n, E, d, D, rng, deadline, iters):
    """Double-edge-swap annealing to reach zero bad pairs. Returns edge list or None."""
    N = n
    adjl = [[] for _ in range(N)]
    for a, b in E:
        adjl[a].append(b)
        adjl[b].append(a)
    if max(len(x) for x in adjl) > d:
        return None
    nbr = np.empty((d, N), dtype=np.int64)
    for v in range(N):
        row = adjl[v]
        for l in range(d):
            nbr[l, v] = row[l] if l < len(row) else v  # pad with self (harmless in OR)
    E = [[a, b] for a, b in E]
    eset = {a * N + b for a, b in E}
    cost = _unreached_pairs(nbr, N, D)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i1 = rng.randrange(len(E))
        i2 = rng.randrange(len(E))
        if i1 == i2:
            continue
        a1, b1 = E[i1]
        a2, b2 = E[i2]
        if a1 == a2 or b1 == b2:
            continue
        if a1 * N + b2 in eset or a2 * N + b1 in eset:
            continue
        _replace(nbr, a1, b1, b2)
        _replace(nbr, b1, a1, a2)
        _replace(nbr, a2, b2, b1)
        _replace(nbr, b2, a2, a1)
        c2 = _unreached_pairs(nbr, N, D)
        T = max(0.2, 1.5 * (1.0 - it / iters))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            eset.discard(a1 * N + b1)
            eset.discard(a2 * N + b2)
            eset.add(a1 * N + b2)
            eset.add(a2 * N + b1)
            E[i1] = [a1, b2]
            E[i2] = [a2, b1]
            cost = c2
        else:
            _replace(nbr, a1, b2, b1)
            _replace(nbr, b1, a2, a1)
            _replace(nbr, a2, b1, b2)
            _replace(nbr, b2, a1, a2)

    if cost != 0:
        return None
    return [(a, b) for a, b in E]


def _insert_pair(n, E, d, rng):
    """Insert two vertices x (A) and y (B): detach d-1 disjoint edges (a_i, b_i), join x to each b_i,
    y to each a_i, and x to y. Degrees of old vertices are unchanged. Returns (n+2, edges) or None."""
    need = d - 1
    if need < 1 or not E:
        return None
    chosen = []
    for _ in range(20):
        order = list(range(len(E)))
        rng.shuffle(order)
        used_a, used_b, chosen = set(), set(), []
        for idx in order:
            a, b = E[idx]
            if a in used_a or b in used_b:
                continue
            used_a.add(a)
            used_b.add(b)
            chosen.append((idx, a, b))
            if len(chosen) == need:
                break
        if len(chosen) == need:
            break
    else:
        return None
    drop = {c[0] for c in chosen}
    x, y = n, n + 1
    newE = [e for i, e in enumerate(E) if i not in drop]
    for _, a, b in chosen:
        newE.append((x, b))
        newE.append((a, y))
    newE.append((x, y))
    return n + 2, newE


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    search_deadline = start + 0.5 * budget
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

    # New phase: insert a vertex pair, then repair the defects by double-edge-swap annealing.
    if d >= 3 and time.monotonic() < deadline:
        cur_n = best_n
        cur_E = _orient(best[0], best[1])
        while time.monotonic() < deadline:
            ins = _insert_pair(cur_n, cur_E, d, rng)
            if ins is None:
                break
            n2, E2 = ins
            res = _anneal(n2, E2, d, D, rng, deadline, _ANNEAL_ITERS)
            if res is None:
                continue
            if lib.is_valid(n2, res, d, D):
                cur_n, cur_E = n2, res
                consider(n2, res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
