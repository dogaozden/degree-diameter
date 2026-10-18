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
# Shared helpers.
# ----------------------------------------------------------------------------

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
# NEW: degree-preserving split growth with bitset-based repair.
#
# Split pair: pick d B-vertices y_i and, for each, one neighbour x_i (all x_i
# distinct). Add w (side A) joined to all y_i and w2 (side B) joined to all x_i,
# and delete the edges (x_i, y_i) by redirecting them: y_i -> w, x_i -> w2.
# Every old vertex keeps its degree, and w, w2 get degree d, so the graph stays
# bipartite with max degree d and gains 2 vertices. Distances can grow, so the
# graph is repaired by degree-preserving 2-switches with simulated annealing.
#
# The cost is the number of unordered vertex pairs at distance > D, computed
# with packed uint64 bitsets in numpy. Graphs far from the Moore bound have
# slack, so a split often needs only a few repair moves.
# ----------------------------------------------------------------------------

_POP16 = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _bad_pairs_bits(nbr, D):
    """Unordered pairs at distance > D. nbr is (n, d) int64, with -1 for empty slots."""
    n = nbr.shape[0]
    W = (n + 63) // 64
    idx = np.arange(n, dtype=np.int64)
    reach = np.zeros((n, W), dtype=np.uint64)
    reach[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(D):
        # The last row of ext is zero, so the -1 padding contributes nothing.
        ext = np.vstack([reach, np.zeros((1, W), dtype=np.uint64)])
        new = reach | np.bitwise_or.reduce(ext[nbr], axis=1)
        if np.array_equal(new, reach):
            break
        reach = new
    pop = int(_POP16[reach.view(np.uint16)].sum())
    return (n * n - pop) // 2


def _set_nb(nb, u, old, new):
    """Replace neighbour `old` of row u by `new` (the entry must exist)."""
    j = int(np.flatnonzero(nb[u] == old)[0])
    nb[u, j] = new


def _split_pair(nbr, colors, d, rng):
    """Add a degree-preserving pair (w in side A, w2 in side B). Returns (nbr, colors) or None."""
    n = nbr.shape[0]
    B = [int(v) for v in np.flatnonzero(colors == 1)]
    if len(B) < d:
        return None
    ys = rng.sample(B, d)
    used = set()
    xs = []
    pairs = []
    for y in ys:
        cand = [int(v) for v in nbr[y] if v >= 0 and int(v) not in used]
        if not cand:
            return None
        x = rng.choice(cand)
        used.add(x)
        xs.append(x)
        pairs.append((y, x))
    out = np.full((n + 2, d), -1, dtype=np.int64)
    out[:n] = nbr
    w, w2 = n, n + 1
    for y, x in pairs:
        _set_nb(out, y, x, w)    # y_i: edge to x_i becomes edge to w
        _set_nb(out, x, y, w2)   # x_i: edge to y_i becomes edge to w2
    out[w, :] = ys
    out[w2, :] = xs
    return out, np.append(colors, [0, 1]).astype(np.int64)


def _repair(nbr, colors, d, D, rng, deadline, max_moves):
    """Annealing over degree-preserving 2-switches on A-B edges. Returns (nbr, cost)."""
    cost = _bad_pairs_bits(nbr, D)
    if cost == 0:
        return nbr, 0
    A = [int(v) for v in np.flatnonzero(colors == 0)]
    nA = len(A)
    if nA < 2:
        return nbr, cost
    c0 = float(max(cost, 1))
    for t in range(max_moves):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.05 * c0 * (1.0 - t / max_moves))
        x1 = A[rng.randrange(nA)]
        x2 = A[rng.randrange(nA)]
        if x1 == x2:
            continue
        j = rng.randrange(d)
        k = rng.randrange(d)
        y1 = int(nbr[x1, j])
        y2 = int(nbr[x2, k])
        if y1 < 0 or y2 < 0 or y1 == y2:
            continue
        if (nbr[x1] == y2).any() or (nbr[x2] == y1).any():
            continue
        # 2-switch: (x1,y1),(x2,y2) -> (x1,y2),(x2,y1). Degrees are unchanged.
        nbr[x1, j] = y2
        nbr[x2, k] = y1
        _set_nb(nbr, y1, x1, x2)
        _set_nb(nbr, y2, x2, x1)
        c2 = _bad_pairs_bits(nbr, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            nbr[x1, j] = y1
            nbr[x2, k] = y2
            _set_nb(nbr, y1, x2, x1)
            _set_nb(nbr, y2, x1, x2)
    return nbr, cost


def _nbr_edges(nbr):
    edges = set()
    for u in range(nbr.shape[0]):
        for v in nbr[u]:
            v = int(v)
            if v >= 0:
                edges.add((min(u, v), max(u, v)))
    return sorted(edges)


def _grow_by_splits(best, d, D, rng, deadline, nmax=7000):
    """Repeatedly add split pairs, keeping each one only if it repairs to diameter D."""
    n, edges = best
    adj = lib.adjacency(n, edges)
    if max((len(a) for a in adj), default=0) > d:
        return None
    col = _bipartition(n, adj)
    if col is None:
        return None
    nbr = np.full((n, d), -1, dtype=np.int64)
    for u in range(n):
        for j, v in enumerate(adj[u]):
            nbr[u, j] = v
    colors = np.array(col, dtype=np.int64)
    fails = 0
    grown = False
    while time.monotonic() < deadline and fails < 3 and nbr.shape[0] + 2 <= nmax:
        res = _split_pair(nbr, colors, d, rng)
        if res is None:
            fails += 1
            continue
        nb2, col2 = res
        nb2, cost = _repair(nb2, col2, d, D, rng, deadline, 300)
        if cost == 0:
            nbr, colors = nb2, col2
            fails = 0
            grown = True
        else:
            fails += 1
    if not grown:
        return None
    return nbr.shape[0], _nbr_edges(nbr)


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
# Every layer is a permutation, so every vertex gets degree d exactly.
#
# Moves: voltage move (random block), layer-swap move, defect-targeted
# voltage move. A bandit over base sizes k decides budget per k.
# Each trial stops once its cost has stagnated for `patience` iterations.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))  # ceil, so the order is at least target
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1  # dihedral-type: (a,b)(c,e) = (a + (-1)^b c, b+e)
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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h, built with one numpy broadcast.
    """
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b is set when representative block b is within distance D.

    Left multiplication is an automorphism, so the 2k block starts cover all orbits.
    """
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
    """Number of unreached (representative, vertex) pairs."""
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
            break  # stagnated: give the bandit a fresh start
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            # Layer-swap move: exchange the B-targets of two A-blocks in one layer.
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

        # Voltage move: defect-targeted with probability 0.4, otherwise uniform.
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget                       # end of growth/repair
    search_deadline = start + 0.6 * budget          # end of Bi-Cayley search
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

    if D >= 4 and time.monotonic() < search_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley search with a bandit over base sizes k.
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
        res = _search(d, D, k, G, Ts, Invs, rng, search_deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # NEW: grow the best graph by degree-preserving split pairs with bitset repair.
    if D >= 3 and time.monotonic() < deadline and best_n >= 2:
        grown = _grow_by_splits(best, d, D, rng, deadline)
        if grown is not None:
            consider(grown[0], grown[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
