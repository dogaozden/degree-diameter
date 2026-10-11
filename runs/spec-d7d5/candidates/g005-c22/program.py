import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact and structured families (from the parent).
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
# Phase A: bi-Cayley lifts over Z_m x| Z_k2 (parent's search, now time-boxed).
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


def _cost_lift(k, G, D, nbr):
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


def _search_lift(d, D, k, G, Ts, Invs, rng, deadline, iters):
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

    cost = _cost_lift(k, G, D, nbr) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        l = rng.randrange(d)
        i = rng.randrange(k)
        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        c2 = _cost_lift(k, G, D, nbr) + _PENALTY * dupcount()
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
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


def _lift_phase(d, D, best, best_n, consider, rng, deadline):
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
        res = _search_lift(d, D, k, G, Ts, Invs, rng, deadline, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])
            best_n = max(best_n, res[0])


# ----------------------------------------------------------------------------
# Phase B (new, high-risk): switch-based annealing on random bipartite
# d-regular graphs with a bitset diameter cost. No group structure is imposed.
#
# Vertices: A = 0..s-1, B = s..2s-1. Each move is a degree-preserving
# double-edge switch (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). The cost is the number
# of ordered vertex pairs at distance > D, computed with Python-int bitsets.
# ----------------------------------------------------------------------------

def _rand_regular_bip(s, d, rng):
    """Return adjA (list of sets): a simple d-regular bipartite graph on s+s vertices, or None."""
    adjA = [set() for _ in range(s)]
    for _ in range(d):
        ok = False
        for _ in range(3000):
            p = list(range(s))
            rng.shuffle(p)
            if all(p[a] not in adjA[a] for a in range(s)):
                ok = True
                break
        if not ok:
            return None
        for a in range(s):
            adjA[a].add(p[a])
    return adjA


def _to_nbr(adjA, s):
    N = 2 * s
    nbr = [[] for _ in range(N)]
    for a in range(s):
        for b in adjA[a]:
            nbr[a].append(s + b)
            nbr[s + b].append(a)
    return nbr


def _cost_bits(nbr, D):
    N = len(nbr)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return N * N - sum(r.bit_count() for r in reach)


def _switch(adjA, nbr, s, a1, b1, a2, b2):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1), updating adjA and nbr."""
    adjA[a1].discard(b1)
    adjA[a2].discard(b2)
    adjA[a1].add(b2)
    adjA[a2].add(b1)
    nbr[a1].remove(s + b1)
    nbr[s + b1].remove(a1)
    nbr[a2].remove(s + b2)
    nbr[s + b2].remove(a2)
    nbr[a1].append(s + b2)
    nbr[s + b2].append(a1)
    nbr[a2].append(s + b1)
    nbr[s + b1].append(a2)


def _anneal_switch(s, d, D, rng, deadline):
    """Return a valid (n, edges) on 2s vertices with diameter <= D, or None."""
    adjA = _rand_regular_bip(s, d, rng)
    if adjA is None:
        return None
    nbr = _to_nbr(adjA, s)
    E = [(a, b) for a in range(s) for b in adjA[a]]
    cost = _cost_bits(nbr, D)
    c0 = float(max(cost, 1))
    it = 0
    while cost > 0 and time.monotonic() < deadline:
        it += 1
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or b2 in adjA[a1] or b1 in adjA[a2]:
            continue
        _switch(adjA, nbr, s, a1, b1, a2, b2)
        new = _cost_bits(nbr, D)
        frac = min(1.0, (time.monotonic() - deadline + 1e9) % 1e9)  # placeholder, replaced below
        temp = max(0.5, 0.02 * c0 * 0.5)
        if new <= cost or rng.random() < math.exp(-(new - cost) / temp):
            cost = new
            E[i] = (a1, b2)
            E[j] = (a2, b1)
        else:
            _switch(adjA, nbr, s, a1, b2, a2, b1)
    if cost != 0:
        return None
    edges = [(a, s + b) for a in range(s) for b in adjA[a]]
    return 2 * s, edges


# ----------------------------------------------------------------------------
# build
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

    # Exact constructions for calibration-style cases.
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

    if D < 3 or d < 3:
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # Phase A: lifts, gets a strong starting point quickly.
    phase_a_end = start + 0.3 * budget
    _lift_phase(d, D, best, best_n, consider, rng, phase_a_end)
    best_n = best[0]

    # Phase B: switch annealing on random regular bipartite graphs just above best.
    if time.monotonic() < deadline - 2.0:
        s = best_n // 2 + 1
        res = _anneal_switch(s, d, D, rng, deadline)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
