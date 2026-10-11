import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe exact families (used when they apply).
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
# NEW: Haar graphs over non-cyclic abelian groups.
#
# Vertices A_g = g, B_h = G + h for g, h in the group G (order N).
# Connection set S (|S| = d, distinct, WLOG 0 in S):  A_g ~ B_{g+s} for s in S.
# This is bipartite, d-regular, and translation-invariant, so diameter <= D is
# equivalent to every vertex lying within D of A_0 and of B_0.
# Search: annealing over S, with cost = number of unreached (rep, vertex) pairs.
# Non-cyclic abelian groups (Z_a x Z_b, ...) are tried first; cyclic groups are
# already covered by the semidirect-product search below.
# ----------------------------------------------------------------------------

def _divisors(n):
    return [a for a in range(1, n + 1) if n % a == 0]


def _abelian_types(N):
    """Invariant-factor types (m1 | m2 | ...) with product N, rank <= 3."""
    types = [(N,)]
    for a in _divisors(N):
        if a == 1 or a == N:
            continue
        b = N // a
        if b % a == 0:
            types.append((a, b))
    for a in _divisors(N):
        if a < 2:
            continue
        rem = N // a
        for b in _divisors(rem):
            if b < a or b % a:
                continue
            c = rem // b
            if c >= b and c % b == 0:
                types.append((a, b, c))
    return types


def _group_tables(mods):
    """Return (G, ADD, NEG) for the abelian group Z_m1 x ... with element index = mixed-radix code."""
    M = np.array(mods, dtype=np.int64)
    coords = np.array(list(itertools.product(*[range(m) for m in mods])), dtype=np.int64)
    G = coords.shape[0]
    X = (coords[:, None, :] + coords[None, :, :]) % M
    ADD = np.ravel_multi_index(tuple(np.moveaxis(X, 2, 0)), mods)
    NEG = np.ravel_multi_index(tuple(((-coords) % M).T), mods)
    return G, ADD, NEG


def _haar_nbr(G, ADD, NEG, S):
    """Neighbour table (2G, d): rows 0..G-1 are A-side, rows G..2G-1 are B-side."""
    S = np.asarray(S, dtype=np.int64)
    nbr = np.empty((2 * G, len(S)), dtype=np.int64)
    nbr[:G] = G + ADD[:, S]
    nbr[G:] = ADD[:, NEG[S]]
    return nbr


def _haar_unreached(G, nbr, D):
    """Number of (representative, vertex) pairs at distance > D from A_0 and from B_0."""
    N2 = 2 * G
    total = 0
    for src in (0, G):
        seen = np.zeros(N2, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = nbr[front].ravel()
            nb = np.unique(nb[~seen[nb]])
            if nb.size == 0:
                break
            seen[nb] = True
            front = nb
        total += N2 - int(seen.sum())
    return total


def _haar_search(d, D, G, ADD, NEG, rng, deadline, iters):
    """Annealing over connection sets. Returns S (list of group indices) or None."""
    if d > G:
        return None
    S = [0] + rng.sample(range(1, G), d - 1)
    cur = _haar_unreached(G, _haar_nbr(G, ADD, NEG, S), D)
    c0 = float(max(cur, 1))
    for t in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        j = rng.randrange(1, d)
        new = rng.randrange(G)
        if new in S:
            continue
        S2 = list(S)
        S2[j] = new
        c2 = _haar_unreached(G, _haar_nbr(G, ADD, NEG, S2), D)
        temp = max(0.5, 0.05 * c0 * (1.0 - t / iters))
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            S, cur = S2, c2
    if cur != 0:
        return None
    return S


def _abelian_phase(d, D, rng, deadline, consider, best_n_fn):
    """Scan group orders upward from the current best order/2; try non-cyclic abelian groups first."""
    if d < 3:
        return
    g_next = 1
    while time.monotonic() < deadline:
        G = max(g_next, best_n_fn() // 2 + 1, d + 1)
        g_next = G + 1
        types = _abelian_types(G)
        noncyclic = [t for t in types if len(t) > 1]
        rng.shuffle(noncyclic)
        order = noncyclic + [(G,)]
        for mods in order:
            now = time.monotonic()
            if now >= deadline:
                return
            _, ADD, NEG = _group_tables(mods)
            S = _haar_search(d, D, G, ADD, NEG, rng, min(deadline, now + 0.8), 6000)
            if S is not None:
                nbr = _haar_nbr(G, ADD, NEG, S)
                edges = [(g, int(v)) for g in range(G) for v in nbr[g]]
                consider(2 * G, edges)
                break


# ----------------------------------------------------------------------------
# Legacy fallback: bi-Cayley lifts over Z_m x| Z_k2 with annealing.
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


def _legacy_phase(d, D, rng, deadline, consider, best_n_fn):
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        best_n = best_n_fn()
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


# ----------------------------------------------------------------------------
# Entry point.
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

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = [lib.haar_graph(d, range(d))]

    def consider(n, e):
        if n > best[0][0] and lib.is_valid(n, e, d, D):
            best[0] = (n, e)

    def best_n_fn():
        return best[0][0]

    # Exact constructions for calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best[0]

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best[0]

    # Bold new construction: Haar graphs over non-cyclic abelian groups.
    if D >= 3 and d >= 3:
        abel_deadline = min(deadline, start + 0.6 * budget)
        _abelian_phase(d, D, rng, abel_deadline, consider, best_n_fn)

    # Legacy semidirect-product lifts use whatever time remains.
    if time.monotonic() < deadline:
        _legacy_phase(d, D, rng, deadline, consider, best_n_fn)

    if not lib.is_valid(best[0][0], best[0][1], d, D):
        return lib.haar_graph(d, range(d))
    return best[0]
