import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact small constructions (kept from the parent as fallbacks and calibration).
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


def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
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
# Stage 1: bi-Cayley lifts over Z_m x|_r Z_k2 (kept from the parent). These give
# a regular, valid starting graph for the growth stage below.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4, 5, 6)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x|_r Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif rng.random() < 0.3:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
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
    """Return (G, Ts, Invs) for Z_m x|_r Z_k2 (element a*k2+b)."""
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


def _reach_block(k, G, D, nbr, d):
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
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing with stagnation restarts. Returns (n, edges) or None."""
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

    reach = _reach_block(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach_block(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
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
        r2 = _reach_block(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
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
# Stage 2 (new, high-risk): vertex insertion + annealing over degree-preserving
# edge swaps, on the full graph (not restricted to group structure).
#
# Insertion: pick d edges x_k-y_k with distinct x's and distinct y's. Add a new
# A-vertex a and a new B-vertex b. Replace each x_k-y_k by x_k-b and a-y_k.
# All degrees stay d, bipartiteness is kept, and no duplicate edges appear.
# The diameter may break; annealing with double-edge swaps repairs it. The cost
# is the number of unordered pairs at distance > D (bitset BFS in numpy).
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _full_cost(n, nbr, D):
    """Number of unordered vertex pairs at distance > D in a graph given by neighbour rows nbr (n, d)."""
    W = (n + 63) // 64
    reach = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n, dtype=np.int64)
    reach[idx, idx >> 6] = np.uint64(1) << (idx & 63).astype(np.uint64)
    for _ in range(D):
        new = reach | np.bitwise_or.reduce(reach[nbr], axis=1)
        if np.array_equal(new, reach):
            break
        reach = new
    pop = int(_POP8[reach.view(np.uint8)].sum())
    return (n * n - pop) // 2


def _swap(nbr, x1, i1, x2, i2, y1, y2):
    """Replace edges x1-y1, x2-y2 by x1-y2, x2-y1 in place (A-side x, B-side y)."""
    nbr[x1, i1] = y2
    nbr[x2, i2] = y1
    j = np.flatnonzero(nbr[y1] == x1)[0]
    nbr[y1, j] = x2
    j = np.flatnonzero(nbr[y2] == x2)[0]
    nbr[y2, j] = x1


def _anneal(n, nbr, side, d, D, rng, deadline, max_moves, cost):
    """Double-edge-swap annealing. Modifies nbr in place. Returns the final cost (0 = success)."""
    A = np.flatnonzero(side == 0)
    T = 0.5
    for t in range(max_moves):
        if cost == 0:
            break
        if (t & 31) == 0 and time.monotonic() > deadline:
            break
        x1 = int(A[rng.randrange(len(A))])
        x2 = int(A[rng.randrange(len(A))])
        if x1 == x2:
            continue
        i1 = rng.randrange(d)
        i2 = rng.randrange(d)
        y1 = int(nbr[x1, i1])
        y2 = int(nbr[x2, i2])
        if y1 == y2:
            continue
        if (nbr[x1] == y2).any() or (nbr[x2] == y1).any():
            continue
        _swap(nbr, x1, i1, x2, i2, y1, y2)
        c2 = _full_cost(n, nbr, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _swap(nbr, x1, i1, x2, i2, y2, y1)  # undo
    return cost


def _regular_state(n, edges, d):
    """Return (n, nbr, side) for a d-regular bipartite valid graph, else None."""
    adj = lib.adjacency(n, edges)
    if any(len(a) != d for a in adj):
        return None
    color = _bipartition(n, adj)
    if color is None:
        return None
    return n, np.array(adj, dtype=np.int64), np.array(color, dtype=np.int64)


def _insert_pair(n, nbr, side, d, rng):
    """Insert one A-vertex and one B-vertex, preserving regularity. Returns (n', nbr', side') or None."""
    A = np.flatnonzero(side == 0)
    order = list(range(len(A) * d))
    rng.shuffle(order)
    usedx, usedy, picks = set(), set(), []
    for e in order:
        x = int(A[e // d])
        y = int(nbr[x, e % d])
        if x in usedx or y in usedy:
            continue
        usedx.add(x)
        usedy.add(y)
        picks.append((x, y))
        if len(picks) == d:
            break
    if len(picks) < d:
        return None
    a, b = n, n + 1
    nn = np.full((n + 2, d), -1, dtype=np.int64)
    nn[:n] = nbr
    side2 = np.concatenate([side, np.array([0, 1], dtype=np.int64)])
    for k, (x, y) in enumerate(picks):
        j = np.flatnonzero(nn[x] == y)[0]
        nn[x, j] = b
        j = np.flatnonzero(nn[y] == x)[0]
        nn[y, j] = a
        nn[a, k] = y
        nn[b, k] = x
    return n + 2, nn, side2


def _edges_of(n, nbr, side):
    out = []
    for x in np.flatnonzero(side == 0):
        for y in nbr[int(x)]:
            out.append((int(x), int(y)))
    return out


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

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions: return immediately on calibration-style cases.
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

    if d < 3:
        return best

    # Stage 1: lift search gives a larger regular starting graph.
    stage1_end = start + 0.4 * budget
    while time.monotonic() < stage1_end:
        k = rng.choice(_KS)
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best[0]:
            continue
        res = _search(d, D, k, G, Ts, Invs, rng, stage1_end, 4000, 1200)
        if res is not None:
            consider(res[0], res[1])

    # Stage 2: grow by vertex insertion + annealing repair.
    st = _regular_state(best[0], best[1], d)
    if st is None:
        h = lib.haar_graph(d, range(d))
        st = _regular_state(h[0], h[1], d)
    if st is None:
        return best
    cur_n, cur_nbr, cur_side = st

    while time.monotonic() < deadline:
        res = _insert_pair(cur_n, cur_nbr, cur_side, d, rng)
        if res is None:
            break
        n2, nb2, s2 = res
        cost = _full_cost(n2, nb2, D)
        if cost > 0:
            cost = _anneal(n2, nb2, s2, d, D, rng, deadline, 1500, cost)
        if cost == 0:
            e2 = _edges_of(n2, nb2, s2)
            if lib.is_valid(n2, e2, d, D):
                cur_n, cur_nbr, cur_side = n2, nb2, s2
                if n2 > best[0]:
                    best = (n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
