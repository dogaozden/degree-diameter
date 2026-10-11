import itertools
import math
import random
import time

import numpy as np

import lib


_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_PENALTY = 1000
_KS = (1, 2, 3, 4)


# ----------------------------------------------------------------------------
# Exact / safe families (used for small D and as fallbacks).
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
# Phase A: bi-Cayley lifts over Z_m x| Z_k2 (structured search, as in the parent).
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            return m, 1, 1
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


def _bicayley_phase(d, D, rng, deadline, best_n):
    """Run bi-Cayley searches until deadline; return a validated (n, edges) larger than best_n, or None."""
    found = None
    while time.monotonic() < deadline:
        k = rng.choice(_KS)
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 3000)
        if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
            best_n, found = res[0], res
    return found


# ----------------------------------------------------------------------------
# Phase B (new): unstructured repair search on a d-regular bipartite graph.
#
# Graph kept as nbr (n x d): nbr[v] lists neighbours of v (global ids).
# Side A = isA[v] True. Moves are degree-preserving edge switches
# (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), scored by the number of ordered
# vertex pairs at distance > D (computed with bitmask reachability).
# Growth adds a pair (x in A, y in B) by pair insertion, then anneals the
# switches until the diameter defect is zero.
# ----------------------------------------------------------------------------

def _nbr_from(n, edges, d, color):
    """Build (nbr, isA) for a d-regular bipartite graph, or return None."""
    rows = [[] for _ in range(n)]
    for u, v in edges:
        rows[u].append(v)
        rows[v].append(u)
    if any(len(r) != d for r in rows):
        return None
    nbr = np.array(rows, dtype=np.int64)
    isA = np.array([c == 0 for c in color], dtype=bool)
    return nbr, isA


def _to_edges(n, nbr, isA):
    edges = []
    for a in np.flatnonzero(isA):
        for b in nbr[a]:
            edges.append((int(a), int(b)))
    return edges


def _init_bits(n):
    W = (n + 63) // 64
    init = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n)
    init[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    return init


def _cost(n, nbr, d, D, init):
    """Return (total ordered pairs at distance > D, per-vertex defect array)."""
    reach = init
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[:, l]]
        if np.array_equal(new, reach):
            break
        reach = new
    rowbits = _POP8[reach.view(np.uint8)].sum(axis=1)
    defect = n - rowbits
    return int(defect.sum()), defect


def _rep(row, old, new):
    i = int(np.argmax(row == old))
    row[i] = new


def _apply_switch(nbr, a1, b1, a2, b2):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1) in place."""
    _rep(nbr[a1], b1, b2)
    _rep(nbr[b1], a1, a2)
    _rep(nbr[a2], b2, b1)
    _rep(nbr[b2], a2, a1)


def _add_pair(n, nbr, isA, d, rng):
    """Pair insertion on copies: returns (n+2, nbr2, isA2) or None."""
    A_ids = np.flatnonzero(isA)
    order = [int(a) for a in A_ids]
    rng.shuffle(order)
    chosen = []
    used = set()
    for a in order:
        if len(chosen) == d - 1:
            break
        b = int(nbr[a, rng.randrange(d)])
        if b in used:
            continue
        used.add(b)
        chosen.append((a, b))
    if len(chosen) < d - 1:
        return None
    x, y = n, n + 1
    nb = np.vstack([nbr, np.zeros((2, d), dtype=np.int64)])
    flags = np.concatenate([isA, np.array([True, False], dtype=bool)])
    for i, (a, b) in enumerate(chosen):
        _rep(nb[a], b, y)
        _rep(nb[b], a, x)
        nb[x, i] = b
        nb[y, i] = a
    nb[x, d - 1] = y
    nb[y, d - 1] = x
    return n + 2, nb, flags


def _anneal(n, nbr, isA, A_ids, d, D, rng, deadline, iters):
    """Switch-based annealing on the defect cost. Returns True if cost reaches 0."""
    init = _init_bits(n)
    cost, defect = _cost(n, nbr, d, D, init)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 2.0 * (1.0 - t / iters) + 0.05
        if rng.random() < 0.5:
            bad = np.flatnonzero(defect)
            v = int(bad[rng.randrange(len(bad))]) if len(bad) else rng.randrange(n)
        else:
            v = rng.randrange(n)
        w = int(nbr[v, rng.randrange(d)])
        if bool(isA[v]):
            a1, b1 = v, w
        else:
            a1, b1 = w, v
        a2 = int(A_ids[rng.randrange(len(A_ids))])
        b2 = int(nbr[a2, rng.randrange(d)])
        if a1 == a2 or b1 == b2 or (nbr[a1] == b2).any() or (nbr[a2] == b1).any():
            continue
        _apply_switch(nbr, a1, b1, a2, b2)
        c2, d2 = _cost(n, nbr, d, D, init)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost, defect = c2, d2
        else:
            _apply_switch(nbr, a1, b2, a2, b1)
    return cost == 0


def _repair(n, nbr, isA, d, D, rng, deadline):
    """Grow by pairs, repairing defects by annealing. Returns the last valid (n, nbr, isA)."""
    saved = (n, nbr.copy(), isA.copy())
    fails = 0
    while time.monotonic() < deadline and fails < 8:
        res = _add_pair(saved[0], saved[1], saved[2], d, rng)
        if res is None:
            break
        n2, nb2, isA2 = res
        A_ids = np.flatnonzero(isA2)
        if _anneal(n2, nb2, isA2, A_ids, d, D, rng, deadline, 800):
            saved = (n2, nb2, isA2)
            fails = 0
        else:
            fails += 1
    return saved


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
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

    # Exact constructions for calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < start + 0.3 * budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase A: structured bi-Cayley search (safe base, about 60% of the budget).
    try:
        found = _bicayley_phase(d, D, rng, start + 0.6 * budget, best_n)
        if found is not None:
            consider(found[0], found[1])
    except Exception:
        pass

    # Phase B: unstructured repair-growth starting from the best d-regular graph.
    try:
        color = _two_color(best_n, best[1])
        built = _nbr_from(best_n, best[1], d, color) if color is not None else None
        if built is not None and d >= 3:
            nb, isA = built
            n2, nb2, isA2 = _repair(best_n, nb, isA, d, D, rng, deadline)
            if n2 > best_n:
                consider(n2, _to_edges(n2, nb2, isA2))
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
