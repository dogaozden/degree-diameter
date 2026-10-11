import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Legacy pipeline (parent program): exact constructions, Bi-Cayley lift search,
# and slack extension. Kept as the safe baseline and as the starting point for
# the new growth phase.
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
    """True if at least d vertices have degree < d (the minimum needed to attach one new vertex)."""
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


def _legacy_build(d, D, seed, time_limit):
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

        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ar = lib.araujo_lopez_graph(d - 2)
                consider(ar[0], ar[1])
            except Exception:
                pass

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
# New phase: unlifted growth + annealing on the full graph.
#
# Instead of searching lifts, we work on the explicit bipartite graph.
#   * Growth move: add a new A-vertex x and a new B-vertex y. Each step takes
#     an edge (a, b), rewires it to (a, y), and adds (x, b). Degrees of all old
#     vertices stay exactly d, and x and y reach degree d after d steps.
#   * Repair move: degree-preserving double-edge swap, which keeps the
#     bipartition and all degrees. Cost = number of ordered pairs at distance > D,
#     computed with bitset BFS over numpy uint64 rows.
# Growth stages are kept only if annealing reaches cost 0, so the result is
# always valid. The best legacy graph is the fallback.
# ----------------------------------------------------------------------------

_POP16 = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _reach_full(n, nbr, D):
    """Bitset rows: bit w of row v is set when w is within distance D of v."""
    d = nbr.shape[1]
    W = (n + 63) // 64
    reach = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n)
    reach[idx, idx // 64] = np.uint64(1) << (idx % 64).astype(np.uint64)
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[:, l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _cost(n, nbr, D):
    """Number of ordered pairs (v, w), v != w, at distance > D; 0 means valid diameter."""
    reach = _reach_full(n, nbr, D)
    tot = int(_POP16[reach.view(np.uint16)].sum())
    return n * n - tot


def _rep(nbr, v, old, new):
    """Replace neighbour `old` by `new` in the row of v."""
    row = nbr[v]
    k = int(np.flatnonzero(row == old)[0])
    row[k] = new


def _swap(nbr, a1, b1, a2, b2):
    """Remove edges (a1,b1), (a2,b2); add (a1,b2), (a2,b1). Degrees are preserved."""
    _rep(nbr, a1, b1, b2)
    _rep(nbr, b2, a2, a1)
    _rep(nbr, a2, b2, b1)
    _rep(nbr, b1, a1, a2)


def _anneal(n, d, D, nbr, EA, EB, rng, deadline, T0):
    """Double-edge-swap annealing on cost. Mutates nbr, EA, EB. Returns True iff cost reaches 0."""
    M = len(EA)
    cost = _cost(n, nbr, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    temp = T0
    it = 0
    while cost > 0:
        if (it & 31) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            temp = max(0.5, T0 * (1.0 - (now - t0) / span))
        it += 1
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a1 = int(EA[i]); b1 = int(EB[i])
        a2 = int(EA[j]); b2 = int(EB[j])
        if a1 == a2 or b1 == b2:
            continue
        if np.any(nbr[a1] == b2) or np.any(nbr[a2] == b1):
            continue
        _swap(nbr, a1, b1, a2, b2)
        EB[i] = b2
        EB[j] = b1
        c2 = _cost(n, nbr, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            _swap(nbr, a1, b2, a2, b1)
            EB[i] = b1
            EB[j] = b2
    return cost == 0


def _grow_once(n, nbr, EA, EB, d, rng):
    """Add vertices x (A side, id n) and y (B side, id n+1), each with degree d; old degrees are unchanged."""
    x, y = n, n + 1
    M0 = len(EA)
    nbr2 = np.full((n + 2, d), -1, dtype=np.int64)
    nbr2[:n] = nbr
    EAl = EA.tolist()
    EBl = EB.tolist()
    Ay = set()   # A-vertices already adjacent to y
    Bx = set()   # B-vertices already adjacent to x
    ops = 0
    tries = 0
    while ops < d and tries < 200000:
        tries += 1
        e = rng.randrange(M0)
        a = EAl[e]
        b = EBl[e]
        if b == y:
            continue
        if a in Ay or b in Bx:
            continue
        _rep(nbr2, a, b, y)
        _rep(nbr2, b, a, x)
        nbr2[x, ops] = b
        nbr2[y, ops] = a
        EBl[e] = y
        EAl.append(x)
        EBl.append(b)
        Ay.add(a)
        Bx.add(b)
        ops += 1
    if ops < d:
        raise RuntimeError("growth step failed")
    return n + 2, nbr2, np.array(EAl, dtype=np.int64), np.array(EBl, dtype=np.int64)


def _to_edges(n, nbr):
    out = []
    for v in range(n):
        for w in nbr[v].tolist():
            if v < w:
                out.append((v, w))
    return out


def _growth(n, edges, d, D, rng, deadline):
    """Repeatedly grow by two vertices and anneal back to valid. Returns (n, edges) or None."""
    adj = lib.adjacency(n, edges)
    if any(len(a) != d for a in adj):
        return None
    color = _bipartition(n, adj)
    if color is None:
        return None
    nbr = np.array(adj, dtype=np.int64)
    EAl, EBl = [], []
    for u, v in edges:
        if color[u] == 0:
            EAl.append(u)
            EBl.append(v)
        else:
            EAl.append(v)
            EBl.append(u)
    EA = np.array(EAl, dtype=np.int64)
    EB = np.array(EBl, dtype=np.int64)

    grown = False
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 1.0:
            break
        n2, nbr2, EA2, EB2 = _grow_once(n, nbr, EA, EB, d, rng)
        stage_dl = min(deadline, now + max(2.0, 0.6 * remaining))
        ok = _anneal(n2, d, D, nbr2, EA2, EB2, rng, stage_dl, 20.0)
        if not ok:
            break
        n, nbr, EA, EB = n2, nbr2, EA2, EB2
        grown = True
    if not grown:
        return None
    return n, _to_edges(n, nbr)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)

    # Calibration-style cases and the trivial cases use the legacy pipeline unchanged.
    if D < 5 or d < 3:
        return _legacy_build(d, D, seed, time_limit)

    # For D >= 5: legacy gets a short share of the budget, growth gets the rest.
    legacy = _legacy_build(d, D, seed, 0.42 * T)
    n0, e0 = legacy
    if not lib.is_valid(n0, e0, d, D):
        legacy = lib.haar_graph(d, range(d))
        n0, e0 = legacy

    deadline = start + min(0.88 * T, T - 6.0)
    rng = random.Random(seed ^ 0x5F3759DF)
    try:
        res = _growth(n0, e0, d, D, rng, deadline)
    except Exception:
        res = None

    if res is not None and res[0] > n0 and lib.is_valid(res[0], res[1], d, D):
        return res
    return legacy
