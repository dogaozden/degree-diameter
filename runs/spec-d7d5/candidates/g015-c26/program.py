import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact and baseline families.
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
# NEW (bold) family: bi-Cayley lifts over the affine group AGL(1, q).
#
# Elements are maps x -> a x + b over GF(q), a != 0, so |G| = q(q-1), which is
# non-abelian and not a semidirect product of cyclic groups of the form used
# elsewhere. Base sizes k = 1 or 2 per side. Darts (i, j, s) join
# A_{i,g} to B_{j, g*s} for every g. Left multiplication is an automorphism,
# so a BFS from the 2k identity vertices covers every orbit. The cost is the
# number of unreached (source, vertex) pairs within distance D.
#
# Each vertex has exactly d darts, so the graph is d-regular and bipartite.
# Failure is possible; the caller keeps the best valid graph found so far.
# ----------------------------------------------------------------------------

_AGL_CACHE = {}


def _agl_tables(q):
    """Return (G, M, inv) for AGL(1, q): M[g, h] = index of g*h, inv[g] = index of g^-1.

    Element (a, b) is coded as (a-1)*q + b, with identity at index 0.
    """
    if q in _AGL_CACHE:
        return _AGL_CACHE[q]
    F = lib.GF(q)
    A = np.array([a for a in range(1, q) for _ in range(q)], dtype=np.int64)
    B = np.array([b for _ in range(1, q) for b in range(q)], dtype=np.int64)
    # (a,b)*(c,e) = (a c, a e + b)
    pa = F.mul_table[A[:, None], A[None, :]]
    pb = F.add_table[F.mul_table[A[:, None], B[None, :]], B[:, None]]
    M = ((pa - 1) * q + pb).astype(np.int64)
    G = M.shape[0]
    inv = np.argmax(M == 0, axis=1).astype(np.int64)
    _AGL_CACHE[q] = (G, M, inv)
    return _AGL_CACHE[q]


def _agl_pairs(d, k, x):
    """Dart slots (i, j). For k = 2, x darts go A0-B0 and x go A1-B1; d-x go A0-B1 and A1-B0."""
    if k == 1:
        return [(0, 0)] * d
    return [(0, 0)] * x + [(0, 1)] * (d - x) + [(1, 0)] * (d - x) + [(1, 1)] * x


def _agl_cost(k, G, M, inv, D, pairs, S):
    """Unreached (source, vertex) pairs within distance D, for the bi-Cayley graph."""
    N = 2 * k * G
    ar = np.arange(G, dtype=np.int64)
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    arcs = []
    for (i, j), s in zip(pairs, S):
        a_idx = i * G + ar
        b_base = (k + j) * G
        arcs.append((a_idx, b_base + M[:, s], b_base + ar, i * G + M[:, inv[s]]))
    for _ in range(D):
        new = reach.copy()
        for a_idx, b_for_a, b_idx, a_for_b in arcs:
            new[a_idx] |= reach[b_for_a]
            new[b_idx] |= reach[a_for_b]
        if np.array_equal(new, reach):
            break
        reach = new
    return 2 * k * N - int(_POP[reach].sum())


def _agl_edges(k, G, M, pairs, S):
    N = 2 * k * G
    edges = set()
    for (i, j), s in zip(pairs, S):
        col = M[:, s].tolist()
        for g in range(G):
            edges.add((i * G + g, (k + j) * G + col[g]))
    return N, sorted(edges)


def _agl_search(k, G, M, inv, D, pairs, rng, deadline, iters):
    """Annealing over voltages. Darts in one (i, j) class keep distinct voltages. Returns (n, edges) or None."""
    P = len(pairs)
    classes = {}
    for p, pr in enumerate(pairs):
        classes.setdefault(pr, []).append(p)
    S = [0] * P
    for members in classes.values():
        vals = rng.sample(range(G), len(members))
        for p, v in zip(members, vals):
            S[p] = v
    cost = _agl_cost(k, G, M, inv, D, pairs, S)
    c0 = float(max(cost, 1))
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        p = rng.randrange(P)
        members = classes[pairs[p]]
        used = {S[q] for q in members if q != p}
        new = rng.randrange(G)
        if new in used:
            continue
        old = S[p]
        S[p] = new
        c2 = _agl_cost(k, G, M, inv, D, pairs, S)
        temp = max(0.3, 0.02 * c0 * (1.0 - t / iters))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[p] = old
    if cost != 0:
        return None
    return _agl_edges(k, G, M, pairs, S)


def _agl_candidates(d, best_n):
    """(n, q, k) options with n = 2kq(q-1) above best_n, sorted by n ascending."""
    cands = []
    for q in range(3, 33):
        if not lib.is_prime_power(q):
            continue
        G = q * (q - 1)
        for k in (1, 2):
            n = 2 * k * G
            if n > best_n and G >= d:
                cands.append((n, q, k))
    cands.sort()
    return cands


def _agl_phase(d, D, rng, deadline, consider, state):
    """Round-robin over AGL candidates, with short time slices and random restarts."""
    while time.monotonic() < deadline:
        cands = _agl_candidates(d, state['best'][0])
        if not cands:
            break
        if rng.random() < 0.6:
            _, q, k = cands[0]
        else:
            _, q, k = rng.choice(cands[:4])
        G, M, inv = _agl_tables(q)
        pairs = _agl_pairs(d, k, rng.randrange(0, d + 1))
        slice_end = min(deadline, time.monotonic() + 4.0)
        res = _agl_search(k, G, M, inv, D, pairs, rng, slice_end, 3000)
        if res is not None:
            consider(res[0], res[1])


# ----------------------------------------------------------------------------
# Parent's bi-Cayley search over semidirect products Z_m x| Z_k2 (fallback).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_SWAP_PROB = 0.3
_STRUCT_PROB = 0.5
_ITERS = 4000


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
    x = rng.randrange(1, G)
    powers = [0]
    for _ in range(d):
        powers.append(int(Ts[x, powers[-1]]))
    ys = [rng.randrange(G) for _ in range(k)]
    layers = [[(i + l) % k for i in range(k)] for l in range(d)]
    S = [[int(Ts[ys[i], powers[l + 1]]) for i in range(k)] for l in range(d)]
    return layers, S


def _random_init(d, k, G, rng):
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    return layers, S


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _cost(k, G, D, nbr):
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.92 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    state = {'best': lib.haar_graph(d, range(d))}

    def consider(n, e):
        if n > state['best'][0] and lib.is_valid(n, e, d, D):
            state['best'] = (n, e)
        return state['best'][0]

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return state['best']

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return state['best']

    # Phase 1 (new): AGL(1,q) bi-Cayley search, about half the budget.
    if D >= 4 and time.monotonic() < deadline:
        agl_deadline = time.monotonic() + 0.5 * (deadline - time.monotonic())
        _agl_phase(d, D, rng, agl_deadline, consider, state)

    # Phase 2 (parent): semidirect-product bi-Cayley search with the remaining time.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        best_n = state['best'][0]
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
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, _ITERS)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    best = state['best']
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
