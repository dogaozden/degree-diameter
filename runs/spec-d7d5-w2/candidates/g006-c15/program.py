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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (as in the parent).
#
# NEW in this version: after the lift search, an "edge-split growth" phase
# (see _grow / _grow_once / _repair below) takes the best regular lift and
# inserts two vertices at a time, keeping every degree exactly d. The inserted
# pair is wired by splitting a matching of d existing edges. Diameter damage is
# then repaired by degree-preserving 2-switch simulated annealing that is
# driven by a numpy bitset reach-cost.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
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
    """Bitmask per vertex: bit b is set when representative block b is within distance D."""
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


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over voltages, layer swaps and defect-targeted moves. Returns (n, edges) or None."""
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
# Edge-split growth (new in this version).
#
# A d-regular bipartite graph on n vertices gains two vertices a (side A) and
# b (side B) while staying d-regular: pick a matching of d edges u_i-v_i
# (u_i in A, v_i in B), delete them, and join a to every v_i and b to every u_i.
# Degrees are unchanged and the graph stays bipartite. The diameter may now
# fail, so degree-preserving 2-switches (u1-v1, u2-v2 -> u1-v2, u2-v1) are
# annealed until the bitset reach-cost is zero.
# ----------------------------------------------------------------------------

def _colors(n, adj):
    """2-colouring of the graph (BFS); returns list of 0/1 per vertex."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        st = [s]
        while st:
            u = st.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    st.append(v)
    return col


def _bitreach(n, nbr, D):
    """Bitset reach matrix: row v has bit w set when dist(v, w) <= D. nbr is (n, d) int array."""
    W = (n + 63) // 64
    reach = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n)
    reach[idx, idx // 64] = np.uint64(1) << (idx % 64).astype(np.uint64)
    for _ in range(D):
        new = reach | np.bitwise_or.reduce(reach[nbr], axis=1)
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached_bits(n, reach):
    """Number of ordered vertex pairs at distance more than D."""
    return n * n - int(np.unpackbits(reach.view(np.uint8)).sum())


def _repair(n, nbr, side, d, D, rng, deadline):
    """Anneal 2-switches in place until the diameter condition holds. Returns True on success."""
    A = np.flatnonzero(side == 0)
    reach = _bitreach(n, nbr, D)
    cost = _unreached_bits(n, reach)
    while cost > 0 and time.monotonic() < deadline:
        u1 = int(A[rng.randrange(len(A))])
        j1 = rng.randrange(d)
        v1 = int(nbr[u1, j1])
        u2 = int(A[rng.randrange(len(A))])
        j2 = rng.randrange(d)
        v2 = int(nbr[u2, j2])
        if u1 == u2 or v1 == v2 or (nbr[u1] == v2).any() or (nbr[u2] == v1).any():
            continue
        k1 = int(np.flatnonzero(nbr[v1] == u1)[0])
        k2 = int(np.flatnonzero(nbr[v2] == u2)[0])
        nbr[u1, j1] = v2
        nbr[u2, j2] = v1
        nbr[v1, k1] = u2
        nbr[v2, k2] = u1
        r2 = _bitreach(n, nbr, D)
        c2 = _unreached_bits(n, r2)
        temp = max(0.5, 0.05 * cost)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            nbr[u1, j1] = v1
            nbr[u2, j2] = v2
            nbr[v1, k1] = u1
            nbr[v2, k2] = u2
    return cost == 0


def _grow_once(n, nbr, side, d, D, rng, deadline):
    """Insert one vertex pair by edge-splitting a random matching, then repair. Returns new state or None."""
    A = np.flatnonzero(side == 0)
    us, vs = [], []
    tries = 0
    while len(us) < d and tries < 500:
        tries += 1
        u = int(A[rng.randrange(len(A))])
        if u in us:
            continue
        v = int(nbr[u, rng.randrange(d)])
        if v in vs:
            continue
        us.append(u)
        vs.append(v)
    if len(us) < d:
        return None
    nb = np.vstack([nbr, np.full((2, d), -1, dtype=np.int64)])
    a_new, b_new = n, n + 1
    for u, v in zip(us, vs):
        ju = int(np.flatnonzero(nb[u] == v)[0])
        nb[u, ju] = b_new
        jv = int(np.flatnonzero(nb[v] == u)[0])
        nb[v, jv] = a_new
    nb[a_new] = vs
    nb[b_new] = us
    side2 = np.concatenate([side, np.array([0, 1], dtype=np.int64)])
    if _repair(n + 2, nb, side2, d, D, rng, deadline):
        return n + 2, nb, side2
    return None


def _grow(n, edges, d, D, rng, deadline):
    """Repeatedly grow a regular bipartite graph by vertex pairs; return (n, edges) or None."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d for a in adj):
        return None
    col = _colors(n, adj)
    nbr = np.array(adj, dtype=np.int64)
    side = np.array(col, dtype=np.int64)
    base_n = n
    cur_n = n
    while time.monotonic() < deadline:
        cap = min(deadline, time.monotonic() + 8.0)
        res = _grow_once(cur_n, nbr, side, d, D, rng, cap)
        if res is not None:
            cur_n, nbr, side = res
    if cur_n == base_n:
        return None
    out = [(u, int(v)) for u in range(cur_n) if side[u] == 0 for v in nbr[u]]
    return cur_n, out


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.92 * time_limit, time_limit - 4.0))
    deadline = start + budget
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: bi-Cayley lift search (about half the budget).
    split = start + 0.5 * budget

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < split:
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
        res = _search(d, D, k, G, Ts, Invs, rng, split, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Phase 2: edge-split growth from the best graph (new idea).
    if D >= 3 and time.monotonic() < deadline:
        try:
            g2 = _grow(best_n, best[1], d, D, rng, deadline)
        except Exception:
            g2 = None
        if g2 is not None:
            consider(g2[0], g2[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
