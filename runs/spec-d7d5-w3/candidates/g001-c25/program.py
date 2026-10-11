import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / safe baseline families.
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
# New construction: unstructured regular bipartite graphs found by simulated
# annealing over double-edge switches. The objective is the number of ordered
# vertex pairs at distance > D, computed with packed bitsets in numpy.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _identity_bits(n):
    """Packed bitset rows: row v has only bit v set."""
    W = (n + 7) // 8
    P0 = np.zeros((n, W), dtype=np.uint8)
    idx = np.arange(n, dtype=np.int64)
    P0[idx, idx >> 3] = (128 >> (idx & 7)).astype(np.uint8)
    return P0


def _bad_ordered(NB, n, d, D, P0):
    """Number of ordered pairs (u, v) with dist(u, v) > D in the d-regular graph NB."""
    P = P0
    for _ in range(D):
        Q = P.copy()
        for s in range(d):
            Q |= P[NB[s]]
        if np.array_equal(Q, P):
            break
        P = Q
    return n * n - int(_POP8[P].sum())


def _sa_attempt(d, D, n, rng, deadline):
    """Try to find a d-regular bipartite graph on n vertices with diameter <= D. Returns (n, edges) or None."""
    h = n // 2
    if n % 2 or h < d:
        return None
    a = np.arange(h, dtype=np.int64)
    NB = np.empty((d, n), dtype=np.int64)
    for s in range(d):
        NB[s, :h] = h + (a + s) % h   # A-vertex x adjacent to B-vertex (x+s) mod h
        NB[s, h:] = (a - s) % h       # B-vertex y adjacent to A-vertex (y-s) mod h
    E = set()
    for x in range(h):
        for s in range(d):
            E.add((x, h + (x + s) % h))
    P0 = _identity_bits(n)

    def slot_of(v, u):
        for s in range(d):
            if int(NB[s, v]) == u:
                return s
        raise RuntimeError("inconsistent adjacency")

    def propose():
        a1 = rng.randrange(h)
        s1 = rng.randrange(d)
        b1 = int(NB[s1, a1])
        a2 = rng.randrange(h)
        s2 = rng.randrange(d)
        b2 = int(NB[s2, a2])
        if a1 == a2 or b1 == b2 or (a1, b2) in E or (a2, b1) in E:
            return None
        return (a1, s1, b1, slot_of(b1, a1), a2, s2, b2, slot_of(b2, a2))

    def apply(a1, s1, b1, t1, a2, s2, b2, t2):
        NB[s1, a1] = b2
        NB[t2, b2] = a1
        NB[s2, a2] = b1
        NB[t1, b1] = a2
        E.discard((a1, b1))
        E.discard((a2, b2))
        E.add((a1, b2))
        E.add((a2, b1))

    # Mix the circulant start thoroughly before annealing.
    for _ in range(10 * h * d):
        mv = propose()
        if mv is not None:
            apply(*mv)

    cur = _bad_ordered(NB, n, d, D, P0)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        mv = propose()
        if mv is None:
            continue
        apply(*mv)
        new = _bad_ordered(NB, n, d, D, P0)
        frac = min(1.0, (now - t0) / span)
        temp = max(0.2, 0.02 * cur * (1.0 - frac))
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
        else:
            # Undo: switch the two new edges back to the old ones.
            apply(mv[0], mv[1], mv[6], mv[7], mv[4], mv[5], mv[2], mv[3])

    edges = [(x, int(NB[s, x])) for x in range(h) for s in range(d)]
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


def _ladder(d, D, rng, deadline, lo_n, lo_e):
    """Grow the order: geometric steps while successful, then bisection between last success and failure."""
    mb = lib.moore_bound(d, D)
    hi_n = None
    while time.monotonic() < deadline:
        if hi_n is None:
            cand = lo_n + max(2, lo_n // 4)
        else:
            if hi_n - lo_n <= 2:
                break
            cand = (lo_n + hi_n) // 2
        if cand > mb:
            cand = mb
        cand -= cand % 2
        if cand <= lo_n:
            break
        if hi_n is not None and cand >= hi_n:
            break
        now = time.monotonic()
        cap = max(0.5, (deadline - now) * 0.3)
        res = _sa_attempt(d, D, cand, rng, min(deadline, now + cap))
        if res is not None:
            lo_n, lo_e = res
        else:
            hi_n = cand
    return lo_n, lo_e


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (parent search, kept as
# the second stage on the remaining time).
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


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, time_limit - 5.0)
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (calibration-style cases return immediately).
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

    # Stage 1 (new construction): annealed unstructured regular bipartite graphs.
    if d >= 3 and D >= 3:
        sa_deadline = start + 0.65 * total
        n1, e1 = _ladder(d, D, rng, sa_deadline, best_n, best[1])
        consider(n1, e1)

    # Stage 2 (parent): bi-Cayley lifts over semidirect products, starting from the best graph.
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

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
