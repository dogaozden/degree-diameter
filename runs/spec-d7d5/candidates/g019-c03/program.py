import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / safe baseline families.
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


def _as_regular(n, edges, d):
    """Return (nbr, color) if the graph is d-regular and bipartite, else None."""
    adj = lib.adjacency(n, edges)
    if any(len(a) != d for a in adj):
        return None
    color = _bipartition(n, adj)
    if color is None:
        return None
    return np.array(adj, dtype=np.int64), color


def _nbr_edges(nbr):
    """Edge list (u < v) of a regular neighbour table."""
    edges = set()
    for u in range(nbr.shape[0]):
        for v in nbr[u].tolist():
            edges.add((u, v) if u < v else (v, u))
    return sorted(edges)


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (search phase).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
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

    reach = _reach(k, G, D, nbr, d)
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
            r2 = _reach(k, G, D, nbr, d)
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
        r2 = _reach(k, G, D, nbr, d)
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
# NEW: grow-and-repair stage (non-algebraic).
#
# Starting from a d-regular bipartite graph, insert a pair of new vertices
# a (side A) and b (side B) by deleting a matching M of d-1 A-B edges
# (x_i, y_i) and wiring a to every y_i, b to every x_i, and a-b.
# Every old vertex keeps degree d and the graph stays bipartite, so the
# result is again d-regular. Simulated annealing chooses the matching to
# minimise the number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _bad_pairs(nb, D):
    """Number of unordered vertex pairs at distance > D, via bitset BFS in numpy."""
    N = nb.shape[0]
    W = (N + 63) // 64
    idx = np.arange(N)
    reach = np.zeros((N, W), dtype=np.uint64)
    reach[idx, idx // 64] = np.uint64(1) << (idx % 64).astype(np.uint64)
    for _ in range(D):
        new = reach | np.bitwise_or.reduce(reach[nb], axis=1)
        if np.array_equal(new, reach):
            break
        reach = new
    total = int(_POP8[reach.view(np.uint8)].sum())
    return (N * N - total) // 2


def _insert_pair(nbr, color, d, D, rng, deadline, restarts=4, iters=250):
    """Try to add two vertices keeping d-regularity and diameter <= D. Returns (nbr, color) or None."""
    n = nbr.shape[0]
    m = d - 1
    A_edges = [(x, int(y)) for x in range(n) if color[x] == 0 for y in nbr[x].tolist()]
    if len(A_edges) < m:
        return None
    a, b = n, n + 1
    new_color = list(color) + [0, 1]

    def build(sel):
        nb = np.empty((n + 2, d), dtype=np.int64)
        nb[:n] = nbr
        xs, ys = [], []
        for t in sel:
            x, y = A_edges[t]
            xs.append(x)
            ys.append(y)
            j = int(np.flatnonzero(nb[x] == y)[0])
            nb[x, j] = b
            j = int(np.flatnonzero(nb[y] == x)[0])
            nb[y, j] = a
        nb[a, :m] = ys
        nb[a, m] = b
        nb[b, :m] = xs
        nb[b, m] = a
        return nb

    def sample_sel():
        order = rng.sample(range(len(A_edges)), len(A_edges))
        sel, ux, uy = [], set(), set()
        for t in order:
            x, y = A_edges[t]
            if x in ux or y in uy:
                continue
            sel.append(t)
            ux.add(x)
            uy.add(y)
            if len(sel) == m:
                return sel
        return None

    for _ in range(restarts):
        if time.monotonic() > deadline:
            return None
        sel = sample_sel()
        if sel is None:
            return None
        nb = build(sel)
        c = _bad_pairs(nb, D)
        if c == 0:
            return nb, new_color
        temp0 = max(1.0, 0.2 * c)
        for it in range(iters):
            if time.monotonic() > deadline:
                return None
            pos = rng.randrange(m)
            t = rng.randrange(len(A_edges))
            if t in sel:
                continue
            x, y = A_edges[t]
            ok = True
            for i2, s in enumerate(sel):
                if i2 != pos and (A_edges[s][0] == x or A_edges[s][1] == y):
                    ok = False
                    break
            if not ok:
                continue
            new_sel = sel.copy()
            new_sel[pos] = t
            nb2 = build(new_sel)
            c2 = _bad_pairs(nb2, D)
            temp = temp0 * (1.0 - it / iters) + 0.2
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
                sel, c, nb = new_sel, c2, nb2
                if c == 0:
                    return nb, new_color
    return None


def _grow(nbr, color, d, D, rng, deadline):
    """Repeatedly insert vertex pairs while possible. Returns the last valid (nbr, color)."""
    cur, col = nbr, color
    while time.monotonic() < deadline:
        res = _insert_pair(cur, col, d, D, rng, deadline)
        if res is None:
            break
        cur, col = res
    return cur, col


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    search_deadline = start + 0.45 * budget
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

    # Exact constructions.
    pg = None
    gq = None
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

    # Largest d-regular bipartite base found so far (needed for grow-and-repair).
    base = None

    def offer_base(n, e):
        nonlocal base
        reg = _as_regular(n, e, d)
        if reg is not None and (base is None or n > base[0]):
            base = (n, reg[0], reg[1])

    offer_base(best[0], best[1])
    if pg is not None:
        offer_base(pg[0], pg[1])
    if gq is not None:
        offer_base(gq[0], gq[1])

    # Phase 1: bi-Cayley lift search with a bandit over base sizes k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < search_deadline:
        k = pick_k()
        base_size = best_n // (2 * k)
        target = max(2, base_size + 1 + rng.randrange(0, max(2, base_size // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, search_deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])
            offer_base(res[0], res[1])

    # Phase 2: grow-and-repair from the best regular base.
    if base is not None and d >= 3 and time.monotonic() < deadline:
        n0, nbr0, col0 = base
        nb, _ = _grow(nbr0, col0, d, D, rng, deadline)
        if nb.shape[0] > n0:
            consider(nb.shape[0], _nbr_edges(nb))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
