import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact small constructions (kept from the parent for D = 3 and D = 4).
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
# NEW MAIN CONSTRUCTION (D >= 5): unstructured d-regular bipartite graphs,
# grown incrementally and repaired by simulated annealing on 2-switches.
#
# State: nbr (n x d) neighbour table, side (0 = A, 1 = B). The graph stays
# d-regular and simple and bipartite at all times. Cost = number of ordered
# pairs at distance > D, computed with bit-packed reach sets (numpy).
#
# Growth: adding one A-vertex a' and one B-vertex b' is done by taking a
# matching (a_t, b_t), t < d, and replacing each edge a_t-b_t by a_t-b' and
# a'-b_t. Degrees are preserved, so the graph stays d-regular.
# ----------------------------------------------------------------------------

_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _cost(nbr, D):
    """Number of ordered vertex pairs (u, v) with dist(u, v) > D (exact for a regular graph)."""
    n = nbr.shape[0]
    W = (n + 63) // 64
    idx = np.arange(n)
    reach = np.zeros((n, W), dtype=np.uint64)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for l in range(nbr.shape[1]):
            new |= reach[nbr[:, l]]
        if np.array_equal(new, reach):
            break
        reach = new
    pop = int(_POP[reach.view(np.uint16)].sum())
    return n * n - pop


def _insert_pair(nbr, side, d, rng):
    """Return (nbr, side) with two new vertices (one per side), degrees preserved; None on failure."""
    n = nbr.shape[0]
    A = np.flatnonzero(side == 0).tolist()
    pairs = None
    for _ in range(200):
        pa = rng.sample(A, d)
        bs = set()
        cand = []
        ok = True
        for a in pa:
            j = rng.randrange(d)
            b = int(nbr[a, j])
            if b in bs:
                ok = False
                break
            bs.add(b)
            cand.append((a, b, j))
        if ok:
            pairs = cand
            break
    if pairs is None:
        return None
    new = np.zeros((n + 2, d), dtype=np.int64)
    new[:n] = nbr
    a_new, b_new = n, n + 1
    for t, (a, b, j) in enumerate(pairs):
        new[a, j] = b_new                       # a - b  becomes  a - b'
        k = int(np.flatnonzero(new[b] == a)[0])
        new[b, k] = a_new                       # a - b  becomes  a' - b
        new[a_new, t] = b
        new[b_new, t] = a
    nside = np.concatenate([side, np.array([0, 1], dtype=np.int64)])
    return new, nside


def _anneal(nbr, side, D, rng, deadline):
    """2-switch annealing on a regular bipartite graph. Returns (True, nbr) on cost 0, else (False, None)."""
    nbr = nbr.copy()
    n, d = nbr.shape
    A = np.flatnonzero(side == 0)
    cur = _cost(nbr, D)
    if cur == 0:
        return True, nbr
    c0 = float(cur)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while True:
        now = time.monotonic()
        if now > deadline:
            return False, None
        frac = (now - t0) / span
        temp = max(0.3, 0.02 * c0 * (1.0 - frac))

        a1 = int(A[rng.randrange(len(A))])
        j1 = rng.randrange(d)
        b1 = int(nbr[a1, j1])
        a2 = int(A[rng.randrange(len(A))])
        j2 = rng.randrange(d)
        b2 = int(nbr[a2, j2])
        if a1 == a2 or b1 == b2:
            continue
        if (nbr[a1] == b2).any() or (nbr[a2] == b1).any():
            continue
        k1 = int(np.flatnonzero(nbr[b1] == a1)[0])
        k2 = int(np.flatnonzero(nbr[b2] == a2)[0])
        nbr[a1, j1] = b2
        nbr[a2, j2] = b1
        nbr[b1, k1] = a2
        nbr[b2, k2] = a1
        new = _cost(nbr, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
            if cur == 0:
                return True, nbr
        else:
            nbr[a1, j1] = b1
            nbr[a2, j2] = b2
            nbr[b1, k1] = a1
            nbr[b2, k2] = a2


def _grow_search(d, D, deadline, rng):
    """Grow a valid d-regular bipartite graph by repeated insertion and annealing. Returns (nbr, side)."""
    nbr = np.empty((2 * d, d), dtype=np.int64)
    nbr[:d] = np.arange(d, 2 * d)[None, :]
    nbr[d:] = np.arange(d)[None, :]
    side = np.array([0] * d + [1] * d, dtype=np.int64)
    best = (nbr, side)  # K_{d,d} has diameter 2 <= D: always valid
    s = 1
    fails = 0
    while time.monotonic() < deadline:
        cur_nbr, cur_side = best
        grown = True
        for _ in range(s):
            r = _insert_pair(cur_nbr, cur_side, d, rng)
            if r is None:
                grown = False
                break
            cur_nbr, cur_side = r
        if grown:
            now = time.monotonic()
            stage_end = min(deadline, now + max(1.5, 0.2 * (deadline - now)))
            ok, st = _anneal(cur_nbr, cur_side, D, rng, stage_end)
            if ok:
                best = (st, cur_side)
                fails = 0
                s = min(2 * s, max(1, st.shape[0] // 40))
                continue
        if s == 1:
            fails += 1
            if fails >= 2:
                break
        s = max(1, s // 2)
    return best


def _edges_from(nbr, side):
    """Return (n, edges) for a bipartite table; each edge listed once from its A endpoint."""
    A = np.flatnonzero(side == 0)
    edges = [(int(a), int(b)) for a in A for b in nbr[a]]
    return int(nbr.shape[0]), edges


# ----------------------------------------------------------------------------
# Parent's secondary machinery (kept as a second contender for D >= 5):
# bi-Cayley lifts over Z_m x| Z_k2 and slack extension.
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


def _radius_balls(n, adj, radius):
    """Bitmask per vertex: bit x set when x is within distance `radius` of the vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(radius):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = [list(a) for a in lib.adjacency(n, edges)]
    color = _bipartition(n, adj)
    if color is None or D < 2:
        return n, edges
    deg = [len(a) for a in adj]
    radius = D - 1

    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        ball = _radius_balls(n, adj, radius)
        full = (1 << n) - 1
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            accepted = False
            for _ in range(4000):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                cover = 0
                for v in pick:
                    cover |= ball[v]
                if cover != full:
                    continue
                w = n
                edges.extend((v, w) for v in pick)
                adj.append(list(pick))
                for v in pick:
                    adj[v].append(w)
                    deg[v] += 1
                n += 1
                color.append(1 - side)
                deg.append(d)
                spare = [v for v in spare if deg[v] < d]
                grew = True
                accepted = True
                ball = _radius_balls(n, adj, radius)
                full = (1 << n) - 1
            if accepted:
                grew = True
    return n, edges


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
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex over the 2k block representatives."""
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
    """Simulated annealing over bi-Cayley voltages. Returns (n, edges) or None."""
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, time_limit - 5.0)
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 2.5)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
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

    # New construction for D >= 5: annealed regular bipartite growth.
    if D >= 5 and d >= 2:
        ann_deadline = start + 0.55 * budget
        nbr, side = _grow_search(d, D, ann_deadline, rng)
        n_ann, e_ann = _edges_from(nbr, side)
        consider(n_ann, e_ann)

    # Parent's bi-Cayley bandit for the remaining time.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best[0]:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Use spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
