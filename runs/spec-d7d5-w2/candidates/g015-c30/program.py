import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

_POP16 = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (lift search stage).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                r = None
                continue
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


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
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


def _unreached(k, N, reach):
    return 2 * k * N - int(_POP16[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over voltages and layer swaps. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
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
# Bipartition helpers.
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    """Return a proper 2-colouring (list of 0/1), or None if the graph is not bipartite."""
    adj = lib.adjacency(n, edges)
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


# ----------------------------------------------------------------------------
# NEW: swap-annealing with pair growth on the explicit d-regular graph.
#
# The graph is kept as an (n, d) neighbour matrix `nbr` with bipartition `col`
# (colour 0 = side A). Two moves are used:
#   * double-edge swap: edges (a1,b1),(a2,b2) become (a1,b2),(a2,b1). Degrees
#     and bipartition are preserved, and the cost is the number of vertex pairs
#     at distance > D, computed with packed-bit reach sets in numpy.
#   * pair growth: once the cost reaches 0, insert two vertices x (side A) and
#     y (side B) by removing d-1 edges with pairwise distinct endpoints, so the
#     order rises by 2 and the graph stays d-regular and bipartite.
# Every improvement is re-verified with lib.is_valid before it is recorded.
# ----------------------------------------------------------------------------

def _nbr_from_edges(n, edges, d):
    """Return the (n, d) neighbour matrix if the graph is exactly d-regular, else None."""
    lists = [[] for _ in range(n)]
    for u, v in edges:
        lists[u].append(v)
        lists[v].append(u)
    if any(len(L) != d for L in lists):
        return None
    return np.array(lists, dtype=np.int64)


def _edges_of(nbr, col):
    """A-to-B edge list of the neighbour matrix."""
    return [(a, int(b)) for a in np.flatnonzero(col == 0).tolist() for b in nbr[a].tolist()]


def _bad_count(nbr, D):
    """Number of unordered vertex pairs at distance > D (packed-bit BFS in numpy)."""
    n, d = nbr.shape
    W = (n + 63) // 64
    idx = np.arange(n)
    reach = np.zeros((n, W), dtype=np.uint64)
    reach[idx, idx >> 6] = np.left_shift(np.ones(n, dtype=np.uint64), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[:, l]]
        if np.array_equal(new, reach):
            break
        reach = new
    cnt = int(_POP16[reach.view(np.uint16)].sum())
    return (n * n - cnt) // 2


def _pair_insert(nbr, col, d, rng):
    """Grow the graph by 2 vertices (x on side A, y on side B), keeping d-regularity."""
    if d < 2:
        return None
    n = nbr.shape[0]
    pairs = _edges_of(nbr, col)
    rng.shuffle(pairs)
    chosen, ua, ub = [], set(), set()
    for a, b in pairs:
        if len(chosen) == d - 1:
            break
        if a in ua or b in ub:
            continue
        chosen.append((a, b))
        ua.add(a)
        ub.add(b)
    if len(chosen) < d - 1:
        return None
    x, y = n, n + 1
    new = np.empty((n + 2, d), dtype=np.int64)
    new[:n] = nbr
    for a, b in chosen:
        sa = int(np.flatnonzero(nbr[a] == b)[0])
        sb = int(np.flatnonzero(nbr[b] == a)[0])
        new[a, sa] = y
        new[b, sb] = x
    new[x, :d - 1] = [b for _, b in chosen]
    new[x, d - 1] = y
    new[y, :d - 1] = [a for a, _ in chosen]
    new[y, d - 1] = x
    ncol = np.concatenate([col, np.array([0, 1], dtype=col.dtype)])
    return new, ncol


def _try_swap(nbr, A, d, rng):
    """Propose a double-edge swap, or None if the proposal is degenerate."""
    a1 = int(A[rng.randrange(len(A))])
    a2 = int(A[rng.randrange(len(A))])
    if a1 == a2:
        return None
    s1 = rng.randrange(d)
    s2 = rng.randrange(d)
    b1 = int(nbr[a1, s1])
    b2 = int(nbr[a2, s2])
    if b1 == b2:
        return None
    if (nbr[a1] == b2).any() or (nbr[a2] == b1).any():
        return None
    return a1, s1, b1, a2, s2, b2


def _apply_swap(nbr, a1, s1, B1, a2, s2, B2):
    """Replace edges (a1,B1),(a2,B2) by (a1,B2),(a2,B1). Calling it again with (a1,s1,B2,a2,s2,B1) reverts it."""
    nbr[a1, s1] = B2
    nbr[a2, s2] = B1
    sb1 = int(np.flatnonzero(nbr[B1] == a1)[0])
    nbr[B1, sb1] = a2
    sb2 = int(np.flatnonzero(nbr[B2] == a2)[0])
    nbr[B2, sb2] = a1


def _grow_anneal(nbr, col, d, D, rng, deadline, best_n, best_edges):
    """Anneal toward cost 0, then grow by a pair. Returns the best valid (n, edges) found."""
    cur_cost = _bad_count(nbr, D)
    A = np.flatnonzero(col == 0)
    temp = 0.6
    while time.monotonic() < deadline:
        if cur_cost == 0:
            n = nbr.shape[0]
            edges = _edges_of(nbr, col)
            if n > best_n and lib.is_valid(n, edges, d, D):
                best_n, best_edges = n, edges
            res = _pair_insert(nbr, col, d, rng)
            if res is None:
                break
            nbr, col = res
            A = np.flatnonzero(col == 0)
            cur_cost = _bad_count(nbr, D)
            continue
        mv = _try_swap(nbr, A, d, rng)
        if mv is None:
            continue
        a1, s1, b1, a2, s2, b2 = mv
        _apply_swap(nbr, a1, s1, b1, a2, s2, b2)
        c = _bad_count(nbr, D)
        if c <= cur_cost or rng.random() < math.exp(-(c - cur_cost) / temp):
            cur_cost = c
        else:
            _apply_swap(nbr, a1, s1, b2, a2, s2, b1)
    if cur_cost == 0:
        n = nbr.shape[0]
        edges = _edges_of(nbr, col)
        if n > best_n and lib.is_valid(n, edges, d, D):
            best_n, best_edges = n, edges
    return best_n, best_edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    lift_deadline = start + 0.4 * budget
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

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < lift_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Stage 1: bi-Cayley lift search with a bandit over base sizes k.
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
        res = _search(d, D, k, G, Ts, Invs, rng, lift_deadline, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Stage 2: swap-annealing with pair growth on the best d-regular graph.
    if d >= 2 and time.monotonic() < deadline:
        try:
            nbr = _nbr_from_edges(best_n, best[1], d)
            if nbr is not None:
                col_list = _two_color(best_n, best[1])
                if col_list is not None:
                    col = np.array(col_list, dtype=np.int64)
                    n2, e2 = _grow_anneal(nbr, col, d, D, rng, deadline, best_n, best[1])
                    if n2 > best_n:
                        consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
