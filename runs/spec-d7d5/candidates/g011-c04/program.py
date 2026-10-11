import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from the parent).
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
# Parent's bi-Cayley lift search over Z_m x| Z_k2 (kept as the first phase).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
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
    """Geometric-progression start for the bi-Cayley search."""
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
# NEW (bold): unstructured d-regular bipartite graphs repaired by edge switches.
#
# Start from a random d-regular bipartite graph on n vertices (n/2 per side),
# represented as an (n, d) neighbour array. Simulated annealing applies random
# edge switches (a1-b1, a2-b2) -> (a1-b2, a2-b1), which keep every degree equal
# to d and keep the graph simple and bipartite. The cost is the number of
# unordered vertex pairs at distance > D, computed with bitsets.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _random_regular(half, d, rng, steps_cap=200000):
    """Simple d-regular bipartite graph on sides 0..half-1 (A) and half..2half-1 (B), as (n, d) array."""
    n = 2 * half
    nbr = np.empty((n, d), dtype=np.int64)
    ar = np.arange(half, dtype=np.int64)
    used = [set() for _ in range(half)]
    for l in range(d):
        p = list(range(half))
        rng.shuffle(p)
        conf = sum(1 for a in range(half) if p[a] in used[a])
        steps = 0
        while conf and steps < steps_cap:
            steps += 1
            a = rng.randrange(half)
            a2 = rng.randrange(half)
            if a == a2:
                continue
            before = int(p[a] in used[a]) + int(p[a2] in used[a2])
            p[a], p[a2] = p[a2], p[a]
            after = int(p[a] in used[a]) + int(p[a2] in used[a2])
            if after <= before:
                conf += after - before
            else:
                p[a], p[a2] = p[a2], p[a]
        if conf:
            return None
        pa = np.array(p, dtype=np.int64)
        nbr[:half, l] = half + pa
        nbr[half + pa, l] = ar
        for a in range(half):
            used[a].add(p[a])
    return nbr


def _switch(nbr, a1, b1, a2, b2):
    """Remove edges (a1,b1),(a2,b2) and add (a1,b2),(a2,b1). Vertex ids are global."""
    r = np.where(nbr[a1] == b1)[0][0]
    nbr[a1, r] = b2
    r = np.where(nbr[a2] == b2)[0][0]
    nbr[a2, r] = b1
    r = np.where(nbr[b1] == a1)[0][0]
    nbr[b1, r] = a2
    r = np.where(nbr[b2] == a2)[0][0]
    nbr[b2, r] = a1


def _bad_pairs(nbr, n, D, nw):
    """Number of unordered pairs at distance > D (bitset BFS over all sources)."""
    idx = np.arange(n, dtype=np.int64)
    reach = np.zeros((n, nw), dtype=np.uint64)
    reach[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for l in range(nbr.shape[1]):
            new |= reach[nbr[:, l]]
        if np.array_equal(new, reach):
            break
        reach = new
    total = int(_POP8[reach.view(np.uint8)].sum())
    return (n * n - total) // 2


def _repair(n, d, D, rng, deadline):
    """Anneal a random d-regular bipartite graph on n vertices to diameter <= D. Returns nbr or None."""
    half = n // 2
    nbr = None
    while nbr is None and time.monotonic() < deadline:
        nbr = _random_regular(half, d, rng)
    if nbr is None:
        return None
    nw = (n + 63) // 64
    cost = _bad_pairs(nbr, n, D, nw)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        temp = max(0.15, 2.0 * (1.0 - frac))
        a1 = rng.randrange(half)
        a2 = rng.randrange(half)
        if a1 == a2:
            continue
        l1 = rng.randrange(d)
        l2 = rng.randrange(d)
        b1 = int(nbr[a1, l1])
        b2 = int(nbr[a2, l2])
        if b1 == b2 or (nbr[a1] == b2).any() or (nbr[a2] == b1).any():
            continue
        _switch(nbr, a1, b1, a2, b2)
        new = _bad_pairs(nbr, n, D, nw)
        if new <= cost or rng.random() < math.exp(-(new - cost) / temp):
            cost = new
        else:
            _switch(nbr, a1, b2, a2, b1)
    return nbr if cost == 0 else None


def _is_target(d, D):
    return d == 7 and D == 5


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
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

    # Exact constructions: return immediately (calibration-style cases).
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

    target = _is_target(d, D)
    # For the target case, the lift search gets 40% of the budget and the
    # unstructured repair phase gets the rest.
    search_end = start + (0.4 * budget if target else budget)

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < search_end:
        k = pick_k()
        base = best_n // (2 * k)
        tgt = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(tgt, rng)
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

    # Bold phase (target case only): unstructured regular graph repair,
    # growing the order in steps of 2 while each attempt succeeds.
    if target:
        n_try = (best_n // 2 + 1) * 2
        while time.monotonic() < deadline - 1.0:
            remaining = deadline - time.monotonic()
            nbr = _repair(n_try, d, D, rng, time.monotonic() + 0.5 * remaining)
            if nbr is None:
                break
            half = n_try // 2
            edges = [(a, int(nbr[a, l])) for a in range(half) for l in range(d)]
            before = best_n
            consider(n_try, edges)
            if best_n < n_try:
                break
            n_try += 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
