import itertools
import math
import random
import time
from collections import Counter

import numpy as np

import lib


_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_PENALTY = 1000
_KS = (1, 2, 3, 4)


# ----------------------------------------------------------------------------
# Structured safe families (fallbacks).
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x| Z_k2 (structured search, used as the safety net).
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
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
    return 2 * k * N - int(_POP8[reach.astype(np.uint8)].sum()) if False else \
        2 * k * N - int(sum(bin(int(x)).count("1") for x in reach))


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    N = 2 * k * G
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
# NEW construction: unstructured random d-regular bipartite graphs, annealed by
# degree-preserving 2-switches until every pair is within distance D.
# ----------------------------------------------------------------------------

def _rand_regular_bip(s, d, rng):
    """Random d-regular bipartite graph with sides 0..s-1 (A) and s..2s-1 (B); returns (2s, d) array or None."""
    ea = [a for a in range(s) for _ in range(d)]
    eb = [s + b for b in range(s) for _ in range(d)]
    rng.shuffle(eb)
    M = len(ea)
    cnt = Counter(zip(ea, eb))
    it = 0
    while True:
        dup = [i for i in range(M) if cnt[(ea[i], eb[i])] > 1]
        if not dup:
            break
        it += 1
        if it > 2000:
            return None
        for i in dup:
            if cnt[(ea[i], eb[i])] <= 1:
                continue
            j = rng.randrange(M)
            k1 = (ea[i], eb[j])
            k2 = (ea[j], eb[i])
            if k1 == k2 or cnt[k1] or cnt[k2]:
                continue
            cnt[(ea[i], eb[i])] -= 1
            cnt[(ea[j], eb[j])] -= 1
            eb[i], eb[j] = eb[j], eb[i]
            cnt[k1] += 1
            cnt[k2] += 1
    ea_a = np.array(ea, dtype=np.int64)
    eb_a = np.array(eb, dtype=np.int64)
    nbr = np.empty((2 * s, d), dtype=np.int64)
    oa = np.argsort(ea_a, kind="stable")
    nbr[:s] = eb_a[oa].reshape(s, d)
    ob = np.argsort(eb_a, kind="stable")
    nbr[s:] = ea_a[ob].reshape(s, d)
    return nbr


def _bad_pairs(nbr, I_p, D):
    """Ordered pairs at distance > D (0 iff diameter <= D)."""
    n = nbr.shape[0]
    R = I_p
    for _ in range(D):
        R2 = R | np.bitwise_or.reduce(R[nbr], axis=1)
        if np.array_equal(R2, R):
            break
        R = R2
    return n * n - int(_POP8[R].sum())


def _anneal(s, d, D, rng, deadline):
    n = 2 * s
    nbr = _rand_regular_bip(s, d, rng)
    if nbr is None:
        return None
    I_p = np.packbits(np.eye(n, dtype=np.uint8), axis=1)
    cost = _bad_pairs(nbr, I_p, D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cost > 0:
        now = time.monotonic()
        if now > deadline:
            break
        frac = (now - start) / span
        T = 0.2 + 2.0 * (1.0 - frac)
        a1 = rng.randrange(s)
        a2 = rng.randrange(s)
        if a1 == a2:
            continue
        j1 = rng.randrange(d)
        j2 = rng.randrange(d)
        b1 = int(nbr[a1, j1])
        b2 = int(nbr[a2, j2])
        if b1 == b2 or (nbr[a1] == b2).any() or (nbr[a2] == b1).any():
            continue
        cand = nbr.copy()
        cand[a1, j1] = b2
        cand[a2, j2] = b1
        r = int(np.flatnonzero(cand[b1] == a1)[0])
        cand[b1, r] = a2
        r = int(np.flatnonzero(cand[b2] == a2)[0])
        cand[b2, r] = a1
        c = _bad_pairs(cand, I_p, D)
        if c <= cost or rng.random() < math.exp(-(c - cost) / T):
            nbr = cand
            cost = c
    if cost != 0:
        return None
    edges = []
    for a in range(s):
        for b in nbr[a]:
            edges.append((a, int(b)))
    return n, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, min(0.9 * time_limit, time_limit - 6.0))
    final_deadline = start + total
    frac = 0.35 if D >= 5 else 0.6
    search_deadline = start + max(1.0, frac * total)
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

    # Structured bi-Cayley search (safety net, shortened budget for D >= 5).
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    try:
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
            res = _search(d, D, k, G, Ts, Invs, rng, search_deadline, 4000, 1200)
            if res is not None:
                wins[k] += 1
                consider(res[0], res[1])
    except Exception:
        pass

    # New construction: anneal random regular bipartite graphs just above the
    # current best order, growing the side size while annealing succeeds.
    if D >= 5 and d >= 2:
        try:
            s = best_n // 2 + 1
            while time.monotonic() < final_deadline - 0.5 and s >= d:
                res = _anneal(s, d, D, rng, final_deadline)
                if res is None:
                    break
                consider(res[0], res[1])
                s += 1
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
