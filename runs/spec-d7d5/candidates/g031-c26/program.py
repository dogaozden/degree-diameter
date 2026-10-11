import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Baseline families (unchanged parent pipeline, used as the safe fallback and
# as the seed graph for the growth search).
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


def _has_spare(n, edges, d):
    """True if at least d vertices have degree < d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return sum(1 for x in deg if x < d) >= d


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (parent search).
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


def _parent_build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 5.0))
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 3.0)
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

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
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
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if time.monotonic() < final_deadline and _has_spare(best[0], best[1], d):
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


# ----------------------------------------------------------------------------
# NEW: bipartite vertex-insertion with degree-preserving edge-swap annealing.
#
# Starting from a valid bipartite graph (the parent's best), repeatedly insert
# a new pair (a', b') of vertices. a' attaches to d vertices of side B; a
# full B-vertex gives up one edge (y, z), which is rerouted so that z attaches
# to b'. b' also takes spare A-vertices to reach degree d. The new graph has
# bad pairs at distance > D; simulated annealing with double-edge swaps (which
# keep every degree and the bipartition) drives the bad-pair count to zero.
# Each success adds two vertices. Any failure returns the last valid graph.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _to_nbr(n, edges, d, color):
    nbr = -np.ones((n, d), dtype=np.int64)
    cnt = [0] * n
    for u, v in edges:
        u, v = int(u), int(v)
        nbr[u, cnt[u]] = v
        cnt[u] += 1
        nbr[v, cnt[v]] = u
        cnt[v] += 1
    return nbr


def _reach_bits(nbr, D):
    N, d = nbr.shape
    W = (N + 63) // 64
    idx = np.arange(N, dtype=np.int64)
    reach = np.zeros((N, W), dtype=np.uint64)
    reach[idx, idx // 64] = np.uint64(1) << (idx % 64).astype(np.uint64)
    nb = np.where(nbr >= 0, nbr, idx[:, None])
    for _ in range(D):
        new = reach.copy()
        for j in range(d):
            new |= reach[nb[:, j]]
        reach = new
    return reach


def _bad(nbr, D):
    """Number of unordered vertex pairs at distance greater than D."""
    N = nbr.shape[0]
    reach = _reach_bits(nbr, D)
    ones = int(_POP8[reach.view(np.uint8)].sum())
    return (N * N - ones) // 2


def _insert(nbr, col, d, rng):
    N = nbr.shape[0]
    deg = (nbr >= 0).sum(axis=1)
    Bs = [v for v in range(N) if col[v] == 1]
    As = [v for v in range(N) if col[v] == 0 and deg[v] < d]
    if len(Bs) < d:
        return None
    Y = rng.sample(Bs, d)
    a_new, b_new = N, N + 1
    new = -np.ones((N + 2, d), dtype=np.int64)
    new[:N] = nbr
    used = set()
    rerouted = []
    for y in Y:
        if deg[y] < d:
            k = int(np.flatnonzero(new[y] < 0)[0])
            new[y, k] = a_new
        else:
            zs = [int(z) for z in new[y] if z >= 0 and int(z) not in used]
            if not zs:
                return None
            z = rng.choice(zs)
            k = int(np.flatnonzero(new[y] == z)[0])
            new[y, k] = a_new
            k2 = int(np.flatnonzero(new[z] == y)[0])
            new[z, k2] = b_new
            used.add(z)
            rerouted.append(z)
    need = d - len(rerouted)
    spare = [x for x in As if x not in used]
    if len(spare) < need:
        return None
    chosen = rng.sample(spare, need) if need > 0 else []
    for x in chosen:
        k = int(np.flatnonzero(new[x] < 0)[0])
        new[x, k] = b_new
    new[a_new, :d] = Y
    new[b_new, :d] = rerouted + chosen
    return new, col + [0, 1]


def _swap(nbr, Alist, rng):
    """Degree- and bipartition-preserving double-edge swap, in place. Returns True on success."""
    for _ in range(20):
        a1 = Alist[rng.randrange(len(Alist))]
        s1 = np.flatnonzero(nbr[a1] >= 0)
        if s1.size == 0:
            continue
        j1 = int(s1[rng.randrange(s1.size)])
        b1 = int(nbr[a1, j1])
        a2 = Alist[rng.randrange(len(Alist))]
        s2 = np.flatnonzero(nbr[a2] >= 0)
        if s2.size == 0:
            continue
        j2 = int(s2[rng.randrange(s2.size)])
        b2 = int(nbr[a2, j2])
        if a1 == a2 or b1 == b2:
            continue
        if (nbr[a1] == b2).any() or (nbr[a2] == b1).any():
            continue
        nbr[a1, j1] = b2
        nbr[a2, j2] = b1
        k = int(np.flatnonzero(nbr[b1] == a1)[0])
        nbr[b1, k] = a2
        k = int(np.flatnonzero(nbr[b2] == a2)[0])
        nbr[b2, k] = a1
        return True
    return False


def _anneal(nbr, Alist, D, rng, deadline):
    cost = _bad(nbr, D)
    if cost == 0:
        return nbr, 0
    start = time.monotonic()
    total = max(1e-3, deadline - start)
    T0 = 1.0 + 0.02 * cost
    while cost > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - start) / total
        T = max(0.3, T0 * (1.0 - frac))
        cand = nbr.copy()
        if not _swap(cand, Alist, rng):
            continue
        c2 = _bad(cand, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            nbr, cost = cand, c2
    return nbr, cost


def _grow(nbr, col, d, D, rng, deadline):
    cur, ccol = nbr, col
    best = None
    fails = 0
    while time.monotonic() < deadline and fails < 3:
        res = _insert(cur, ccol, d, rng)
        if res is None:
            break
        cand, newcol = res
        now = time.monotonic()
        att = min(deadline, now + max(2.0, 0.5 * (deadline - now)))
        Alist = [v for v in range(len(newcol)) if newcol[v] == 0]
        out, c = _anneal(cand, Alist, D, rng, att)
        if c == 0:
            cur, ccol = out, newcol
            best = (cur, ccol)
            fails = 0
        else:
            fails += 1
    return best


def _nbr_edges(nbr, col):
    N = nbr.shape[0]
    edges = []
    for v in range(N):
        if col[v] == 0:
            for b in nbr[v]:
                if b >= 0:
                    edges.append((v, int(b)))
    return N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if D != 5 or d < 3:
        return _parent_build(d, D, seed, time_limit)

    # Seed graph from the parent pipeline (safe fallback).
    base_n, base_e = _parent_build(d, D, seed, 0.4 * time_limit)
    if base_n <= 0 or not lib.is_valid(base_n, base_e, d, D):
        return lib.haar_graph(d, range(d))

    try:
        color = _bipartition(base_n, lib.adjacency(base_n, base_e))
        if color is None:
            return base_n, base_e
        nbr = _to_nbr(base_n, base_e, d, color)
        rng = random.Random((seed * 1000003) ^ 0x5EED)
        deadline = start + time_limit - 6.0
        best = _grow(nbr, color, d, D, rng, deadline)
        if best is not None:
            n2, e2 = _nbr_edges(best[0], best[1])
            if n2 > base_n and lib.is_valid(n2, e2, d, D):
                return n2, e2
    except Exception:
        pass
    return base_n, base_e
