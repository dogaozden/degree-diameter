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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2.
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
# Bipartition colouring.
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    """Return a proper 2-colouring (list of 0/1) of the graph, or None if it is not bipartite."""
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
# NEW: switch-repair pair growth.
#
# Pair insertion adds two vertices x (side A), y (side B) and removes d-1
# matched edges, so every vertex keeps degree d and the graph stays bipartite,
# but coverage is usually broken. Instead of rejecting the step, the defects
# are repaired by degree- and bipartition-preserving 2-switches
#   (a1,b1),(a2,b2) -> (a1,b2),(a2,b1)
# chosen to hit a vertex that still has unreached partners. A step is kept
# only if the repair reaches zero defects within distance D, and the total
# unreached-pair count is the annealing cost. Reach sets are bit-packed so
# each evaluation is a handful of row gathers.
# ----------------------------------------------------------------------------

def _nbr_from_edges(n, E, d):
    """Neighbour table (n, d) for a d-regular oriented edge list E of (a, b) pairs."""
    arr = np.asarray(E, dtype=np.int64)
    src = np.concatenate([arr[:, 0], arr[:, 1]])
    dst = np.concatenate([arr[:, 1], arr[:, 0]])
    order = np.argsort(src, kind="stable")
    return dst[order].reshape(n, d)


def _bad_ordered(n, nbr, D):
    """Return (ordered unreached pair count, per-vertex unreached count array)."""
    W = (n + 7) // 8
    R = np.zeros((n, W), dtype=np.uint8)
    idx = np.arange(n)
    R[idx, idx >> 3] = (np.left_shift(1, idx & 7)).astype(np.uint8)
    d = nbr.shape[1]
    for _ in range(D):
        NR = R.copy()
        for l in range(d):
            NR |= R[nbr[:, l]]
        if np.array_equal(NR, R):
            break
        R = NR
    cnt = _POP8[R].sum(axis=1)
    return n * n - int(cnt.sum()), n - cnt


def _repair(n, E, d, D, rng, max_evals, deadline):
    """Anneal 2-switches until the d-regular graph on n vertices has diameter <= D. Returns (ok, E)."""
    E = list(E)
    Eset = set(E)
    nbr = _nbr_from_edges(n, E, d)
    cost, unr = _bad_ordered(n, nbr, D)
    evals = 0
    while cost > 0 and evals < max_evals and time.monotonic() < deadline:
        evals += 1
        bad_vs = np.flatnonzero(unr)
        u = int(bad_vs[rng.randrange(bad_vs.size)])
        touch = [t for t, (a, b) in enumerate(E) if a == u or b == u]
        i = touch[rng.randrange(len(touch))]
        j = rng.randrange(len(E))
        if j == i:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in Eset or (a2, b1) in Eset:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        Eset.discard((a1, b1))
        Eset.discard((a2, b2))
        Eset.add((a1, b2))
        Eset.add((a2, b1))
        nbr2 = _nbr_from_edges(n, E, d)
        c2, unr2 = _bad_ordered(n, nbr2, D)
        temp = max(0.5, 3.0 * (1.0 - evals / max_evals))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, unr, nbr = c2, unr2, nbr2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            Eset.discard((a1, b2))
            Eset.discard((a2, b1))
            Eset.add((a1, b1))
            Eset.add((a2, b2))
    if cost == 0:
        return True, E
    return False, None


def _pair_insert(n, E, d, rng):
    """Remove d-1 matched edges and add x (side A) and y (side B) joined to each other and the cut ends."""
    order = list(range(len(E)))
    rng.shuffle(order)
    chosen, ua, ub = [], set(), set()
    for t in order:
        a, b = E[t]
        if a in ua or b in ub:
            continue
        chosen.append(t)
        ua.add(a)
        ub.add(b)
        if len(chosen) == d - 1:
            break
    if len(chosen) < d - 1:
        return None
    cs = set(chosen)
    x, y = n, n + 1
    out = [E[t] for t in range(len(E)) if t not in cs]
    for t in chosen:
        a, b = E[t]
        out.append((x, b))
        out.append((a, y))
    out.append((x, y))
    return out


def _grow(n, edges, d, D, rng, deadline):
    """Repeatedly add a pair of vertices and repair; keep only steps that reach zero defects."""
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    fails = 0
    while time.monotonic() < deadline and fails < 25:
        cand = _pair_insert(n, E, d, rng)
        if cand is None:
            break
        ok, res = _repair(n + 2, cand, d, D, rng, 800, deadline)
        if ok:
            n += 2
            E = res
            fails = 0
        else:
            fails += 1
    return n, [(int(a), int(b)) for a, b in E]


def _is_regular(n, edges, d):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.90 * time_limit, time_limit - 5.0))
    deadline = start + budget
    search_deadline = start + 0.55 * budget
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

    if D >= 4 and time.monotonic() < search_deadline:
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
        res = _search(d, D, k, G, Ts, Invs, rng, search_deadline, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Switch-repair pair growth on the best regular graph found so far.
    try:
        if _is_regular(best_n, best[1], d) and time.monotonic() < deadline:
            n2, e2 = _grow(best_n, best[1], d, D, rng, deadline)
            if n2 > best_n:
                consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
