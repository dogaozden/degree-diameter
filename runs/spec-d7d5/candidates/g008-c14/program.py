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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (parent search, kept).
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
    """Geometric-progression start for the voltage search."""
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
# NEW for the d=7, D=5 target: degree-preserving edge-switch annealing on a
# general bipartite graph, with vertex-pair growth.
#
# Each candidate is a d-regular bipartite graph stored as:
#   adj[v]  : neighbour list (global ids), length d
#   E       : list of edges (a, b), a on side A, b on side B
#   eset    : set of the same edges, for duplicate checks
#   nbr     : numpy mirror of adj, updated in place
# The cost is the number of ordered unreached pairs within distance D, computed
# with bit-packed reachability sets (numpy uint64 words).
# Growth adds one A vertex p and one B vertex q: take a matching of d edges
# (a_i, b_i), replace them by (a_i, q) and (p, b_i). Degrees stay d.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _pair_cost(n, nbr, D):
    """Ordered vertex pairs (v, w) with dist(v, w) > D, via bit-packed BFS frontiers."""
    W = (n + 63) // 64
    reach = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n, dtype=np.int64)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for j in range(nbr.shape[1]):
            new |= reach[nbr[:, j]]
        if np.array_equal(new, reach):
            break
        reach = new
    pop = int(_POP8[reach.view(np.uint8)].sum())
    return n * n - pop


def _bipartition(n, edges):
    """Return a 0/1 colouring of the vertices, or None if the graph is not bipartite."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _setup(n, E, d):
    """Build adjacency lists and the edge set from oriented edges E."""
    adj = [[] for _ in range(n)]
    eset = set()
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
        eset.add((a, b))
    return adj, eset


def _random_regular(N, d, rng):
    """Random d-regular bipartite graph on sides [0, N) and [N, 2N); returns oriented edges or None."""
    for _ in range(50):
        eset = set()
        ok = True
        for _ in range(d):
            placed = False
            for _ in range(3000):
                perm = list(range(N))
                rng.shuffle(perm)
                if all((a, N + perm[a]) not in eset for a in range(N)):
                    placed = True
                    break
            if not placed:
                ok = False
                break
            for a in range(N):
                eset.add((a, N + perm[a]))
        if ok:
            return list(eset)
    return None


def _pick_swap(E, eset, rng):
    """Propose a double-edge swap of two random edges; return indices or None if invalid."""
    m = len(E)
    i = rng.randrange(m)
    j = rng.randrange(m)
    if i == j:
        return None
    a, b = E[i]
    c, e = E[j]
    if a == c or b == e:
        return None
    if (a, e) in eset or (c, b) in eset:
        return None
    return i, j


def _do_swap(E, eset, adj, nbr, i, j):
    """Replace edges (a,b),(c,e) by (a,e),(c,b). Calling it again with the same i, j reverts."""
    a, b = E[i]
    c, e = E[j]
    E[i] = (a, e)
    E[j] = (c, b)
    eset.discard((a, b))
    eset.discard((c, e))
    eset.add((a, e))
    eset.add((c, b))
    ka = adj[a].index(b)
    adj[a][ka] = e
    nbr[a, ka] = e
    kb = adj[b].index(a)
    adj[b][kb] = c
    nbr[b, kb] = c
    kc = adj[c].index(e)
    adj[c][kc] = b
    nbr[c, kc] = b
    ke = adj[e].index(c)
    adj[e][ke] = a
    nbr[e, ke] = a


def _anneal(E, eset, adj, nbr, n, D, rng, deadline, iters, T0):
    """Metropolis search over edge switches. Returns the final cost (0 means valid)."""
    cost = _pair_cost(n, nbr, D)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        sw = _pick_swap(E, eset, rng)
        if sw is None:
            continue
        i, j = sw
        _do_swap(E, eset, adj, nbr, i, j)
        temp = max(0.5, T0 * (1.0 - t / iters))
        c2 = _pair_cost(n, nbr, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            _do_swap(E, eset, adj, nbr, i, j)
    return cost


def _grow(E, eset, adj, n, d, rng):
    """Add vertices p (side A, id n) and q (side B, id n+1) using a d-edge matching. Returns False if impossible."""
    p, q = n, n + 1
    idxs = list(range(len(E)))
    rng.shuffle(idxs)
    usedA, usedB, chosen = set(), set(), []
    for t in idxs:
        a, b = E[t]
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        chosen.append(t)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return False
    chosen_set = set(chosen)
    newE = [E[t] for t in range(len(E)) if t not in chosen_set]
    for t in chosen:
        a, b = E[t]
        eset.discard((a, b))
    adj.append([])
    adj.append([])
    for t in chosen:
        a, b = E[t]
        ka = adj[a].index(b)
        adj[a][ka] = q
        kb = adj[b].index(a)
        adj[b][kb] = p
        adj[p].append(b)
        adj[q].append(a)
        newE.append((a, q))
        newE.append((p, b))
        eset.add((a, q))
        eset.add((p, b))
    E[:] = newE
    return True


def _phase_b(d, D, best, rng, deadline):
    """Anneal a regular bipartite graph, then grow it while zero-cost states are reached.

    Starts from `best` if it is d-regular and bipartite; otherwise from a random
    d-regular graph on 2*567 vertices. Returns (n, edges) for the last zero-cost state, or None.
    """
    n0, edges0 = best
    E = None
    color = _bipartition(n0, edges0)
    if color is not None:
        E0 = [(u, v) if color[u] == 0 else (v, u) for u, v in edges0]
        adj, eset = _setup(n0, E0, d)
        if all(len(a) == d for a in adj):
            E = E0
            n = n0
    if E is None:
        N = 567
        E = _random_regular(N, d, rng)
        if E is None:
            return None
        n = 2 * N
        adj, eset = _setup(n, E, d)

    nbr = np.array(adj, dtype=np.int64)
    cost = _anneal(E, eset, adj, nbr, n, D, rng, deadline, 3000, 30.0)
    if cost != 0:
        return None
    best_state = (n, list(E))
    while time.monotonic() < deadline:
        if not _grow(E, eset, adj, n, d, rng):
            break
        n += 2
        nbr = np.array(adj, dtype=np.int64)
        cost = _anneal(E, eset, adj, nbr, n, D, rng, deadline, 3000, 30.0)
        if cost != 0:
            break
        best_state = (n, list(E))
    return best_state


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

    target = (d == 7 and D == 5)
    search_end = start + (0.6 * budget if target else budget)

    # Main search with the bandit over base sizes k (parent routine).
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < search_end:
        k = pick_k()
        base = best_n // (2 * k)
        target_order = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target_order, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, search_end, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Bold phase for the d=7, D=5 target: edge-switch annealing plus vertex growth.
    if target and time.monotonic() < deadline - 2.0:
        try:
            res = _phase_b(d, D, (best_n, best[1]), rng, deadline - 1.0)
        except Exception:
            res = None
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
