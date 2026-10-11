"""Bold variant: keep the parent's bi-Cayley voltage search as a fallback, then spend
the remaining budget on a different family: single-orbit bipartite Cayley graphs on
semidirect products Z_m x| Z_k.

A Cayley graph Cay(G, S) on a group G with an index-2 homomorphism phi: G -> Z_2 is
bipartite when every s in S has phi(s) = 1. Vertices are group elements, edges are
g ~ g*s, and vertex transitivity reduces the diameter check to one BFS from the identity.
The search anneals over inverse-closed generator sets (pairs {s, s^-1} plus involutions)
to minimise the number of unreached group elements within distance D.

Every returned graph is checked with lib.is_valid, and the Haar fallback K_{d,d} is kept
if nothing better is found.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / safe baseline families (unchanged from parent).
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
# Parent bi-Cayley voltage search (kept as the first stage).
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
# New stage: single-orbit bipartite Cayley graphs on Z_m x| Z_k.
# ----------------------------------------------------------------------------

def _divisors(n):
    return [k for k in range(1, n + 1) if n % k == 0]


def _cayley_tables(n, k, rng):
    """Multiplication table, inverses, and parity classes for Z_m x| Z_k with m = n // k.

    Returns (M, inv, pair_reps, odd_invs) or None. M[x, y] = x*y.
    pair_reps are odd non-involutions (one per {s, s^-1}); odd_invs are odd involutions.
    """
    m = n // k
    if m % 2 == 0:
        parity = "a"
    elif k % 2 == 0:
        parity = "b"
    else:
        return None
    if m == 1:
        r = 0
    elif k == 1:
        r = 1
    else:
        r = None
        for _ in range(200):
            c = rng.randrange(1, m)
            if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
                r = c
                break
        if r is None:
            return None
    P = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    x = np.arange(n, dtype=np.int64)
    a = x // k
    b = x % k
    M = ((a[:, None] + P[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    phi = (a % 2) if parity == "a" else (b % 2)
    rows, cols = np.nonzero(M == 0)
    inv = np.empty(n, dtype=np.int64)
    inv[rows] = cols
    odd = phi == 1
    invol = inv == x
    pair_reps = np.flatnonzero(odd & ~invol & (x < inv)).tolist()
    odd_invs = np.flatnonzero(odd & invol).tolist()
    return M, inv, pair_reps, odd_invs


def _cay_unreached(n, M, gens, D):
    """Number of group elements at distance > D from the identity in Cay(G, gens)."""
    visited = np.zeros(n, dtype=bool)
    visited[0] = True
    frontier = np.array([0], dtype=np.int64)
    for _ in range(D):
        nb = M[np.ix_(frontier, gens)].ravel()
        nb = np.unique(nb[~visited[nb]])
        if nb.size == 0:
            break
        visited[nb] = True
        frontier = nb
    return n - int(visited.sum())


def _cay_anneal(n, d, D, M, inv, pair_reps, odd_invs, rng, iters, deadline):
    """Anneal an inverse-closed odd generator set of size <= d. Returns gens array or None."""
    options = [p for p in range(d // 2 + 1)
               if (d - 2 * p) <= len(odd_invs) and p <= len(pair_reps)]
    if not options:
        return None
    p = rng.choice(options)
    t = d - 2 * p
    reps = rng.sample(pair_reps, p)
    invs = rng.sample(odd_invs, t)

    def evaluate(reps_, invs_):
        g = []
        for s in reps_:
            g.append(s)
            g.append(int(inv[s]))
        g.extend(invs_)
        arr = np.array(sorted(set(g)), dtype=np.int64)
        dup = len(g) - arr.size
        return _cay_unreached(n, M, arr, D) + _PENALTY * dup, arr

    cost, arr = evaluate(reps, invs)
    c0 = float(max(cost, 1))
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.3, 0.03 * c0 * (1.0 - it / iters))
        if p > 0 and (t == 0 or rng.random() < p / (p + t)):
            i = rng.randrange(p)
            old = reps[i]
            new = rng.choice(pair_reps)
            if new in reps:
                continue
            reps[i] = new
            c2, a2 = evaluate(reps, invs)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, arr = c2, a2
            else:
                reps[i] = old
        else:
            i = rng.randrange(t)
            old = invs[i]
            new = rng.choice(odd_invs)
            if new in invs:
                continue
            invs[i] = new
            c2, a2 = evaluate(reps, invs)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, arr = c2, a2
            else:
                invs[i] = old
    if cost != 0:
        return None
    return arr


def _cay_edges(n, M, arr):
    """Edge list of Cay(G, arr) on vertices 0..n-1 (right multiplication by generators)."""
    g = arr.size
    E = M[:, arr]
    us = np.repeat(np.arange(n, dtype=np.int64), g)
    vs = E.ravel()
    lo = np.minimum(us, vs)
    hi = np.maximum(us, vs)
    keep = lo != hi
    pairs = set(zip(lo[keep].tolist(), hi[keep].tolist()))
    return n, sorted(pairs)


def _cayley_stage(d, D, rng, deadline, best_fn, consider):
    """Random search over even orders just above the current best, on random semidirect groups."""
    while time.monotonic() < deadline:
        b = best_fn()
        lo = b + 1
        hi = b + max(40, b // 8)
        lo_e = lo + (lo % 2)
        hi_e = hi - (hi % 2)
        if hi_e < lo_e:
            return
        n = rng.randrange(lo_e, hi_e + 1, 2)
        k = rng.choice(_divisors(n))
        tabs = _cayley_tables(n, k, rng)
        if tabs is None:
            continue
        M, inv, pr, oi = tabs
        if not pr:
            continue
        arr = _cay_anneal(n, d, D, M, inv, pr, oi, rng, 2500, deadline)
        if arr is not None:
            consider(*_cay_edges(n, M, arr))


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

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
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

    # Split budget: parent voltage search first, then the Cayley stage.
    parent_deadline = start + (0.5 * budget if d >= 3 else budget)

    if D >= 4 and time.monotonic() < parent_deadline:
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

    while time.monotonic() < parent_deadline:
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
        res = _search(d, D, k, G, Ts, Invs, rng, parent_deadline, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # New family: bipartite Cayley graphs, searched just above the current best.
    if d >= 3 and time.monotonic() < deadline:
        try:
            _cayley_stage(d, D, rng, deadline, lambda: best_n, consider)
        except (ValueError, MemoryError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
