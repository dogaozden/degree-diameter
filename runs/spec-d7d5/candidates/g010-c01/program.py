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
# Group tables and sampling (shared by both searches).
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
        m = max(2, -(-target // k2))  # ceil, so the order is at least target
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


def _sample_cayley_group(lo, hi, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with lo <= m*k2 <= hi, mostly nonabelian, or None."""
    if lo > hi:
        return None
    for _ in range(300):
        k2 = rng.choice([1, 2, 2, 3, 4, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24, 27, 28, 30, 36, 40])
        mlo = -(-lo // k2)
        mhi = hi // k2
        if mlo > mhi or mhi < 2:
            continue
        m = rng.randint(max(2, mlo), mhi)
        if k2 == 1:
            return m, 1, 1
        if rng.random() < 0.1:
            r = 1
        else:
            valid = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if not valid:
                continue
            r = rng.choice(valid)
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h, built with one numpy broadcast.
    The identity is element 0.
    """
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = M[g, s] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


# ----------------------------------------------------------------------------
# NEW bold routine: Cayley-type (k = 1) bipartite graphs over nonabelian groups.
#
# Vertices A_g = g and B_h = G + h. Connection set S (|S| = d, identity in S WLOG,
# since right multiplication of S is an isomorphism). Edges A_g ~ B_{g s}.
# Left multiplication is an automorphism, so it suffices to check eccentricities
# from A_1 and B_1. The search is simulated annealing over S with a cheap
# numpy BFS cost: number of vertices unreached within distance D.
# ----------------------------------------------------------------------------

def _cayley_cost(S, G, Ts, Invs, D):
    """Total unreached (root, vertex) pairs over the roots A_1 and B_1."""
    nA = Ts[S]    # nA[l, g] = B-index of A_g's neighbour through s_l
    nB = Invs[S]  # nB[l, h] = A-index of B_h's neighbour through s_l
    total = 0
    for side in (0, 1):
        rA = np.zeros(G, dtype=bool)
        rB = np.zeros(G, dtype=bool)
        if side == 0:
            rA[0] = True
        else:
            rB[0] = True
        for _ in range(D):
            ia = np.flatnonzero(rA)
            ib = np.flatnonzero(rB)
            nb = rB.copy()
            na = rA.copy()
            if ia.size:
                nb[nA[:, ia].ravel()] = True
            if ib.size:
                na[nB[:, ib].ravel()] = True
            if np.array_equal(na, rA) and np.array_equal(nb, rB):
                break
            rA, rB = na, nb
        total += 2 * G - int(rA.sum()) - int(rB.sum())
    return total


def _cayley_anneal(d, G, Ts, Invs, D, rng, deadline, iters):
    """Anneal a connection set S of size d containing the identity. Returns S (list) or None."""
    if G < d:
        return None
    S = [0] + rng.sample(range(1, G), d - 1)
    cost = _cayley_cost(np.array(S, dtype=np.int64), G, Ts, Invs, D)
    for t in range(iters):
        if cost == 0:
            break
        if (t & 63) == 0 and time.monotonic() > deadline:
            break
        temp = max(0.3, 3.0 * (1.0 - t / iters))
        pos = rng.randrange(1, d)
        new = rng.randrange(1, G)
        if new in S:
            continue
        old = S[pos]
        S[pos] = new
        c2 = _cayley_cost(np.array(S, dtype=np.int64), G, Ts, Invs, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[pos] = old
    if cost == 0:
        return S
    return None


# ----------------------------------------------------------------------------
# Parent routine: bi-Cayley lifts with k base vertices per side (kept as a
# second line of search, after the Cayley phase).
# ----------------------------------------------------------------------------

def _structured_init(d, k, G, Ts, rng):
    """Geometric-progression start: layers[l][i] = (i + l) mod k, S[l][i] = y_i * x^(l+1)."""
    x = rng.randrange(1, G)
    powers = [0]  # identity element is index 0
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

    # Phase A (bold): Cayley-type bipartite graphs over nonabelian groups.
    if D >= 3 and d >= 3:
        moore_side = max(1, lib._moore_bound(d, D) // 2)
        c_lo = max(best_n // 2 + 1, int(0.34 * moore_side))
        c_hi = max(c_lo + 2, int(0.40 * moore_side))
        cay_deadline = min(start + 0.65 * budget, deadline)
        while time.monotonic() < cay_deadline:
            g = _sample_cayley_group(c_lo, c_hi, rng)
            if g is None:
                c_lo, c_hi = max(2 * d, c_lo - 5), max(2 * d + 2, c_hi)
                continue
            m, k2, r = g
            G, Ts, Invs = _semidirect_tables(m, k2, r)
            S = _cayley_anneal(d, G, Ts, Invs, D, rng, cay_deadline, 4000)
            if S is not None:
                edges = [(gg, G + int(v)) for s in S for gg, v in enumerate(Ts[s].tolist())]
                consider(2 * G, edges)
                # Shift the Cayley target window above the new best.
                c_lo = max(c_lo, best_n // 2 + 1)
                c_hi = max(c_hi, c_lo + 2)

    # Phase B: bandit over base sizes k (bi-Cayley lifts with k base vertices).
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
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
