import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / safe baseline families (unchanged from the parent).
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
# NEW construction: single-base bi-Cayley graphs (Haar-type) over a group G.
#
# Vertices A_g = g and B_h = n + h. Connection set S (d distinct group elements)
# gives A_g ~ B_{g*s}. Each vertex has degree d. Left multiplication is an
# automorphism, so distances only need checking from A_e and B_e.
# The group is searched over: affine groups AGL(1,q), and semidirect products
# Z_m x| Z_k (including abelian and dihedral-type). Simulated annealing runs over S.
# ----------------------------------------------------------------------------

def _affine_table(q):
    """Multiplication table of AGL(1,q) = F_q x| F_q^*, element (a,u) coded as a*(q-1)+(u-1)."""
    F = lib.GF(q)
    n = q * (q - 1)
    x = np.arange(n, dtype=np.int64)
    A = x // (q - 1)
    U = x % (q - 1) + 1
    mult = F.mul_table
    M = F.add_table[A[:, None], mult[U[:, None], A[None, :]]] * (q - 1) + (mult[U[:, None], U[None, :]] - 1)
    return n, M.astype(np.int64)


def _semi_table(m, k, r):
    """Multiplication table of Z_m x| Z_k: (a,b)(c,e) = (a + r^b c, b + e), coded a*k+b."""
    n = m * k
    x = np.arange(n, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    return n, M.astype(np.int64)


def _build_table(spec):
    if spec[0] == "aff":
        return _affine_table(spec[1])
    return _semi_table(spec[1], spec[2], spec[3])


def _sample_new_group(lo, hi, rng):
    """Return a group spec with order in [lo, hi], or None."""
    aff = [q for q in range(3, 80) if lib.is_prime_power(q) and lo <= q * (q - 1) <= hi]
    if aff and rng.random() < 0.3:
        return ("aff", rng.choice(aff))
    for _ in range(100):
        G = rng.randint(lo, hi)
        divs = [k for k in range(1, min(G // 2, 40) + 1) if G % k == 0]
        if not divs:
            continue
        k = rng.choice(divs)
        m = G // k
        r = 1
        if k >= 2 and m >= 3:
            if k == 2 and rng.random() < 0.3:
                r = m - 1  # dihedral-type
            elif rng.random() < 0.7:
                for _ in range(60):
                    c = rng.randrange(2, m)
                    if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
                        r = c
                        break
        return ("sd", m, k, r)
    return None


def _cayley_search(d, D, n, M, rng, deadline, iters):
    """Anneal a connection set S of size d in the group with table M. Returns (ok, S)."""
    inv = np.argmax(M == 0, axis=1)
    N = 2 * n
    cache = {}

    def nbr_of(s):
        f = np.empty(N, dtype=np.int64)
        f[:n] = n + M[:, s]
        f[n:] = M[:, inv[s]]
        return f

    def getf(s):
        if s not in cache:
            if len(cache) > 300:
                cache.clear()
            cache[s] = nbr_of(s)
        return cache[s]

    def cost_of(S):
        fs = [getf(s) for s in S]
        R = np.zeros((2, N), dtype=bool)
        R[0, 0] = True   # source A_e
        R[1, n] = True   # source B_e
        for _ in range(D):
            new = R.copy()
            for f in fs:
                new |= R[:, f]
            if np.array_equal(new, R):
                break
            R = new
        return 2 * N - int(R.sum())

    S = rng.sample(range(n), d)
    cur = cost_of(S)
    c0 = float(max(cur, 1))
    for t in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.3, 0.05 * c0 * (1.0 - t / iters))
        i = rng.randrange(d)
        new = rng.randrange(n)
        if new in S:
            continue
        S2 = S.copy()
        S2[i] = new
        c2 = cost_of(S2)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            S, cur = S2, c2
    return cur == 0, S


def _cayley_edges(n, M, S):
    edges = []
    g = np.arange(n, dtype=np.int64)
    for s in S:
        edges.extend(zip(g.tolist(), (n + M[:, s]).tolist()))
    return 2 * n, edges


def _phase_cayley(d, D, rng, deadline, best_n_fn, consider):
    while time.monotonic() < deadline:
        lo = best_n_fn() // 2 + 1
        hi = lo + max(3, lo // 12)
        spec = _sample_new_group(lo, hi, rng)
        if spec is None:
            continue
        n, M = _build_table(spec)
        if d > n:
            continue
        ok, S = _cayley_search(d, D, n, M, rng, deadline, 3000)
        if ok:
            consider(*_cayley_edges(n, M, S))


# ----------------------------------------------------------------------------
# Parent's multi-base bi-Cayley search over semidirect products (kept as phase B).
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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (Ts[s, g] = g*s, Invs[s, h] = g with g*s = h)."""
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
# Driver: exact constructions, then new Cayley search (about half the budget),
# then the parent's multi-base search for the remainder. Every candidate is
# checked with lib.is_valid, and K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase A: new single-base Cayley search over affine and semidirect groups.
    if D >= 3 and d >= 2:
        phase_a_end = start + 0.5 * budget
        _phase_cayley(d, D, rng, phase_a_end, lambda: best_n, consider)

    # Phase B: parent's multi-base bandit search over semidirect lifts.
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
