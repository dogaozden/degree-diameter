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
_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
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
# NEW ROUTINE: signed 2-lift annealing.
#
# Given a d-regular simple base graph H on n vertices, its 2-lift H^s has
# vertices (v, t) for t in {0,1} and, for each base edge e = (v, w) with sign
# s_e in {0,1}, the edges (v, t) -- (w, t XOR s_e). The lift is d-regular,
# simple, has 2n vertices and is bipartite whenever H is (layer t of v gets the
# colour of v). We anneal over the signs s_e to minimise the number of pairs at
# distance > D, using a bit-parallel reachability computation over all sources.
# ----------------------------------------------------------------------------

def _lift_nbr(s, inc, other, n):
    """Neighbour table (2n, d) of the signed 2-lift for sign vector s (indexed by base edge)."""
    S = s[inc]
    t0 = other + S * n
    t1 = other + (1 - S) * n
    return np.vstack((t0, t1))


def _lift_cost(nbr, N, D):
    """Number of ordered-pair-of-vertices (u, v) with dist(u, v) > D in a graph given by nbr (N, d)."""
    d = nbr.shape[1]
    W = (N + 63) // 64
    reach = np.zeros((N + 1, W), dtype=np.uint64)  # row N is a zero pad row
    idx = np.arange(N, dtype=np.int64)
    reach[idx, idx >> 6] = np.uint64(1) << (idx & 63).astype(np.uint64)
    for _ in range(D):
        new = reach.copy()
        for j in range(d):
            new[:N] |= reach[nbr[:, j]]
        if np.array_equal(new, reach):
            break
        reach = new
    return N * N - int(_POP8[reach[:N].view(np.uint8)].sum())


def _lift_anneal(n, edges, d, D, rng, deadline, iters):
    """Anneal signs of a 2-lift of a d-regular base graph. Returns (2n, edges) or None."""
    adj = [[] for _ in range(n)]
    for e, (u, v) in enumerate(edges):
        adj[u].append((e, v))
        adj[v].append((e, u))
    for a in adj:
        if len(a) != d or len({w for _, w in a}) != d:
            return None
    inc = np.array([[e for e, _ in a] for a in adj], dtype=np.int64)
    other = np.array([[w for _, w in a] for a in adj], dtype=np.int64)
    E = len(edges)
    N = 2 * n
    s = np.array([rng.randrange(2) for _ in range(E)], dtype=np.int64)
    nbr = _lift_nbr(s, inc, other, n)
    cost = _lift_cost(nbr, N, D)
    c0 = float(max(cost, 1))
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        e = rng.randrange(E)
        s[e] ^= 1
        nbr2 = _lift_nbr(s, inc, other, n)
        c2 = _lift_cost(nbr2, N, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            nbr = nbr2
        else:
            s[e] ^= 1
    if cost != 0:
        return None
    lifted = set()
    for x in range(N):
        for y in nbr[x]:
            y = int(y)
            if x < y:
                lifted.add((x, y))
    return N, sorted(lifted)


# ----------------------------------------------------------------------------
# Growth by edge-switch vertex insertion.
# ----------------------------------------------------------------------------

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


def _grow_step(n, edges, col, d, D, rng, deadline):
    """Try random edge-switch insertions until one keeps diameter <= D. Returns (n+2, edges, col) or None."""
    m = len(edges)
    need = d - 1
    while time.monotonic() < deadline:
        order = list(range(m))
        rng.shuffle(order)
        used_a, used_b, chosen = set(), set(), []
        for idx in order:
            u, v = edges[idx]
            if col[u] == 1:
                u, v = v, u
            if u in used_a or v in used_b:
                continue
            used_a.add(u)
            used_b.add(v)
            chosen.append((idx, u, v))
            if len(chosen) == need:
                break
        if len(chosen) < need:
            continue
        drop = {idx for idx, _, _ in chosen}
        new_edges = [edges[i] for i in range(m) if i not in drop]
        x, y = n, n + 1
        for _, a, b in chosen:
            new_edges.append((x, b))
            new_edges.append((a, y))
        new_edges.append((x, y))
        if lib.within_diameter(n + 2, new_edges, D):
            return n + 2, new_edges, col + [0, 1]
    return None


def _grow(d, D, n, edges, rng, deadline):
    """Repeatedly insert vertex pairs while the graph stays valid. Returns (n, edges)."""
    col = _colours(n, edges)
    while time.monotonic() < deadline:
        res = _grow_step(n, edges, col, d, D, rng, deadline)
        if res is None:
            break
        n, edges, col = res
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    search_end = start + 0.30 * budget
    lift_end = start + 0.85 * budget
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

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    # Phase A: bi-Cayley annealing to find a strong base graph.
    while time.monotonic() < search_end:
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
        res = _search(d, D, k, G, Ts, Invs, rng, search_end, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Phase B: find a bi-Cayley base whose signed 2-lift beats the current best.
    while time.monotonic() < lift_end:
        k = pick_k()
        Gt = max(2, best_n // (4 * k) + 1 + rng.randrange(0, max(2, best_n // (16 * k) + 1)))
        g = _sample_group(Gt, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 4 * k * G <= best_n:
            continue
        sub_end = min(lift_end, time.monotonic() + 4.0)
        res = _search(d, D, k, G, Ts, Invs, rng, sub_end, 4000)
        if res is None:
            continue
        bn, be = res
        lift_deadline = min(lift_end, time.monotonic() + 6.0)
        lifted = _lift_anneal(bn, be, d, D, rng, lift_deadline, 8000)
        if lifted is not None:
            consider(lifted[0], lifted[1])

    # Phase C: spend the remaining time inserting vertex pairs into the best graph.
    if d >= 3 and time.monotonic() < deadline:
        gn, ge = _grow(d, D, best[0], list(best[1]), rng, deadline)
        consider(gn, ge)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
