import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / structured baselines.
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
# Semidirect group tables shared by all bi-Cayley searches.
#
# Group Z_m x| Z_k with element a*k+b, (a,b)(c,e) = (a + r^b c, b + e).
# Ts[s, g] = g*s,  Invs[s, h] = h*s^{-1}  (the g with g*s = h).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _semidirect_tables(m, k2, r):
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


# ----------------------------------------------------------------------------
# NEW construction: systematic enumeration of semidirect groups of a given
# order window, followed by simulated annealing over the connection set of a
# bi-Cayley graph (base = 1 vertex per side, d darts).
#
# Vertices: A_g = g, B_h = G + h. Edge A_g ~ B_{g*s} for s in S (|S| = d).
# Left multiplication is an automorphism, and by the relabelling B_h -> B_{h t^-1}
# we may fix S[0] = identity. Distances are checked by two layered BFS runs,
# one from A_identity and one from B_identity. These two sources cover all
# vertex pairs by vertex-transitivity on each side.
# ----------------------------------------------------------------------------

def _enumerate_groups(lo, hi, deadline):
    """All (m, k, r) with lo <= m*k <= hi (k = 1 cyclic, k >= 2 non-abelian r != 1)."""
    out = []
    for k in range(1, hi + 1):
        if time.monotonic() > deadline:
            break
        m_lo = max(2, -(-lo // k))
        m_hi = hi // k
        for m in range(m_lo, m_hi + 1):
            if k == 1:
                out.append((m, 1, 1))
                continue
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    out.append((m, k, r))
    return out


def _bfs_unreached(G, Ts, Invs, S, D, side):
    """Number of vertices NOT within distance D of the identity vertex on the given side (0=A, 1=B)."""
    visA = np.zeros(G, dtype=bool)
    visB = np.zeros(G, dtype=bool)
    front = np.array([0], dtype=np.int64)
    if side == 0:
        visA[0] = True
    else:
        visB[0] = True
    cur = side
    for _ in range(D):
        if front.size == 0:
            break
        mask = np.zeros(G, dtype=bool)
        if cur == 0:
            idx = np.concatenate([Ts[s][front] for s in S])
            mask[idx] = True
            mask &= ~visB
            visB |= mask
        else:
            idx = np.concatenate([Invs[s][front] for s in S])
            mask[idx] = True
            mask &= ~visA
            visA |= mask
        front = np.flatnonzero(mask)
        cur ^= 1
    return 2 * G - int(visA.sum()) - int(visB.sum())


def _cost_k1(G, Ts, Invs, S, D):
    return _bfs_unreached(G, Ts, Invs, S, D, 0) + _bfs_unreached(G, Ts, Invs, S, D, 1)


def _sa_k1(d, D, G, Ts, Invs, rng, deadline):
    """Anneal the connection set S (|S| = d, S[0] = identity). Returns S or None."""
    if d > G or d < 2:
        return None
    S = [0] + rng.sample(range(1, G), d - 1)
    cost = _cost_k1(G, Ts, Invs, S, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        temp = max(0.25, 3.0 * (1.0 - frac))
        l = 1 + rng.randrange(d - 1)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[l]
        S[l] = new
        c2 = _cost_k1(G, Ts, Invs, S, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[l] = old
    return list(S) if cost == 0 else None


def _k1_edges(G, Ts, S):
    return [(g, G + int(Ts[s][g])) for s in S for g in range(G)]


# ----------------------------------------------------------------------------
# Older multi-block bi-Cayley search (k = 1..4 base vertices per side).
# Kept as a secondary phase for generality.
# ----------------------------------------------------------------------------

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
# Driver.
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

    # Phase 1 (new): enumerate semidirect groups just above the current record
    # order and anneal a single-block bi-Cayley connection set in each.
    if D >= 3 and d >= 2:
        p1_end = start + 0.75 * budget
        W = 60
        CAP = 1500
        while time.monotonic() < p1_end:
            lo = best_n // 2 + 1
            hi = min(lo + W, CAP)
            if lo > hi:
                break
            groups = _enumerate_groups(lo, hi, p1_end)
            groups = [g for g in groups if d <= g[0] * g[1] <= CAP]
            if not groups:
                break
            groups.sort(key=lambda g: g[0] * g[1])
            idx = int(len(groups) * rng.random() ** 2)
            m, k, r = groups[idx]
            G, Ts, Invs = _semidirect_tables(m, k, r)
            now = time.monotonic()
            slice_end = min(p1_end, now + max(1.5, (p1_end - now) / 4.0))
            S = _sa_k1(d, D, G, Ts, Invs, rng, slice_end)
            if S is not None:
                consider(2 * G, _k1_edges(G, Ts, S))

    # Phase 2: multi-block bandit search (old construction family) for the rest.
    if D >= 2:
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
