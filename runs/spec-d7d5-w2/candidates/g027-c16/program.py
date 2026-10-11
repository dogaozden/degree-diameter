import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact and semi-exact baselines (kept as the safe fallback).
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
# Bi-Cayley lifts over semidirect products (previous search, used as baseline).
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


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
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
# NEW construction: simulated annealing over d-regular bipartite graphs.
#
# A bipartite d-regular graph on h+h vertices is stored as two arrays:
#   A_nb[a, s] = B-local index of the s-th neighbour of A-vertex a
#   B_nb[b, t] = A-local index of the t-th neighbour of B-vertex b
# Vertex ids in the full graph: A-vertex a -> a, B-vertex b -> h + b.
#
# Moves are 2-switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which preserve
# regularity and bipartiteness. The cost is the total number of unreached
# (vertex, vertex) pairs at distance > D, computed with bitsets. Growth adds
# two vertices by removing d-1 edges with distinct endpoints, which keeps
# every degree equal to d; the annealer then repairs the new defects.
# ----------------------------------------------------------------------------

def _random_regular(h, d, rng):
    """Random d-regular bipartite A-side array (h x d) with no repeated neighbour in a row."""
    A = np.empty((h, d), dtype=np.int64)
    for l in range(d):
        perm = list(range(h))
        rng.shuffle(perm)
        A[:, l] = perm
    for _ in range(400000):
        S = np.sort(A, axis=1)
        rows = np.flatnonzero((np.diff(S, axis=1) == 0).any(axis=1))
        if rows.size == 0:
            return A
        i = int(rows[rng.randrange(rows.size)])
        vals = A[i].copy()
        cols = [l for l in range(d) if int((vals == vals[l]).sum()) > 1]
        l = cols[rng.randrange(len(cols))]
        j = rng.randrange(h)
        A[i, l], A[j, l] = A[j, l], A[i, l]
    return None


def _build_B(h, d, A_nb):
    B_nb = np.empty((h, d), dtype=np.int64)
    cols = np.arange(h, dtype=np.int64)
    for l in range(d):
        B_nb[A_nb[:, l], l] = cols
    return B_nb


def _full_adj(h, A_nb, B_nb):
    return np.vstack([h + A_nb, B_nb])


def _reach_bits(N, full, D):
    """Bitset per vertex: bit w set when w is within distance D."""
    W = (N + 63) // 64
    R = np.zeros((N, W), dtype=np.uint64)
    idx = np.arange(N, dtype=np.int64)
    R[idx, idx // 64] = np.uint64(1) << (idx % 64).astype(np.uint64)
    for _ in range(D):
        new = R.copy()
        for c in range(full.shape[1]):
            new |= R[full[:, c]]
        if np.array_equal(new, R):
            break
        R = new
    return R


def _deficiency(N, R):
    cnt = _POP8[R.view(np.uint8)].sum(axis=1)
    return N - cnt


def _anneal(h, d, D, A_nb, B_nb, rng, deadline, iters):
    """Anneal 2-switches to zero deficiency. Modifies A_nb/B_nb in place; returns final cost."""
    N = 2 * h
    R = _reach_bits(N, _full_adj(h, A_nb, B_nb), D)
    defi = _deficiency(N, R)
    cost = int(defi.sum())
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.1, 4.0 * (1.0 - t / iters))
        if defi.any() and rng.random() < 0.5:
            bad = np.flatnonzero(defi)
            v = int(bad[rng.randrange(bad.size)])
            if v < h:
                a1 = v
                s1 = rng.randrange(d)
                b1 = int(A_nb[a1, s1])
            else:
                b1 = v - h
                a1 = int(B_nb[b1, rng.randrange(d)])
                s1 = int(np.flatnonzero(A_nb[a1] == b1)[0])
        else:
            a1 = rng.randrange(h)
            s1 = rng.randrange(d)
            b1 = int(A_nb[a1, s1])
        a2 = rng.randrange(h)
        s2 = rng.randrange(d)
        b2 = int(A_nb[a2, s2])
        if a1 == a2 or b1 == b2 or (A_nb[a1] == b2).any() or (A_nb[a2] == b1).any():
            continue
        oldA = A_nb.copy()
        oldB = B_nb.copy()
        A_nb[a1, s1] = b2
        A_nb[a2, s2] = b1
        t1 = int(np.flatnonzero(B_nb[b1] == a1)[0])
        B_nb[b1, t1] = a2
        t2 = int(np.flatnonzero(B_nb[b2] == a2)[0])
        B_nb[b2, t2] = a1
        R2 = _reach_bits(N, _full_adj(h, A_nb, B_nb), D)
        defi2 = _deficiency(N, R2)
        c2 = int(defi2.sum())
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            defi = defi2
        else:
            A_nb[:] = oldA
            B_nb[:] = oldB
    return cost


def _grow(h, d, A_nb, B_nb, rng):
    """Add one A-vertex x and one B-vertex y, keeping all degrees equal to d. None on failure."""
    order = list(range(h * d))
    rng.shuffle(order)
    chosen = []
    ua, ub = set(), set()
    for e in order:
        if len(chosen) == d - 1:
            break
        a, s = divmod(e, d)
        b = int(A_nb[a, s])
        if a in ua or b in ub:
            continue
        chosen.append((a, s, b))
        ua.add(a)
        ub.add(b)
    if len(chosen) < d - 1:
        return None
    x = h
    y = h
    nA = np.vstack([A_nb, np.zeros((1, d), dtype=np.int64)])
    nB = np.vstack([B_nb, np.zeros((1, d), dtype=np.int64)])
    xrow, yrow = [], []
    for a, s, b in chosen:
        nA[a, s] = y
        t = int(np.flatnonzero(B_nb[b] == a)[0])
        nB[b, t] = x
        xrow.append(b)
        yrow.append(a)
    xrow.append(y)
    yrow.append(x)
    nA[h] = xrow
    nB[h] = yrow
    return nA, nB


def _to_edges(h, A_nb):
    return [(a, h + int(b)) for a in range(h) for b in A_nb[a]]


def _anneal_phase(d, D, best, rng, deadline):
    """Grow a d-regular bipartite graph by annealing; keep the largest valid one found."""
    best_n = best[0]
    h = max(d + 1, best_n // 2)
    A_nb = _random_regular(h, d, rng)
    if A_nb is None:
        return best
    B_nb = _build_B(h, d, A_nb)
    while time.monotonic() < deadline:
        cost = _anneal(h, d, D, A_nb, B_nb, rng, deadline, 1500)
        if cost == 0:
            n = 2 * h
            if n > best_n:
                edges = _to_edges(h, A_nb)
                if lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_n = n
            g = _grow(h, d, A_nb, B_nb, rng)
            if g is None:
                break
            A_nb, B_nb = g
            h += 1
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < start + 0.2 * total:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d < 3 or D < 3:
        return best

    # Phase 1 (about 25% of the budget): previous voltage-lift search as a baseline.
    search_deadline = start + 0.25 * total
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

    # Phase 2 (the rest of the budget): annealed bipartite growth.
    try:
        cand = _anneal_phase(d, D, best, rng, deadline)
        if cand[0] > best_n:
            consider(cand[0], cand[1])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
