import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact and algebraic families (kept from the parent as safe baselines).
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
# NEW MAIN ROUTE (bold change): random d-regular bipartite graphs repaired by
# simulated annealing on the number of vertex pairs at distance > D.
#
# The graph is the union of d perfect matchings between sides A and B, stored as
# permutations perms[l] of range(h). Each vertex keeps d distinct neighbours
# (checked on every move), so the graph stays simple and d-regular. The move is
# a transposition of two targets inside one layer. The cost is the number of
# ordered vertex pairs at distance > D, computed on bit-packed reachability
# sets. Unlike the voltage lifts, this does not need a group, so it can reach
# orders that no small group-lift family covers. The size grows whenever a
# valid graph is found.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _clash(perms, d, a):
    """Number of repeated targets for A-vertex a across the d layers (0 means simple)."""
    return d - len({perms[l][a] for l in range(d)})


def _rr_init(d, h, rng):
    """d random permutations of range(h) with no repeated target at any A-vertex, or None."""
    perms = []
    for _ in range(d):
        p = list(range(h))
        rng.shuffle(p)
        perms.append(p)
    for _ in range(2000):
        bad = [a for a in range(h) if _clash(perms, d, a)]
        if not bad:
            return perms
        for a in bad:
            if not _clash(perms, d, a):
                continue
            l = rng.randrange(d)
            a2 = rng.randrange(h)
            before = _clash(perms, d, a) + _clash(perms, d, a2)
            perms[l][a], perms[l][a2] = perms[l][a2], perms[l][a]
            after = _clash(perms, d, a) + _clash(perms, d, a2)
            if after > before and rng.random() > 0.1:
                perms[l][a], perms[l][a2] = perms[l][a2], perms[l][a]
    return None


def _set_layer(nbr, perm, h, l):
    """Write layer l of the neighbour table from the permutation perm (A -> B)."""
    p = np.asarray(perm, dtype=np.int64)
    nbr[l, :h] = h + p
    inv = np.empty(h, dtype=np.int64)
    inv[p] = np.arange(h, dtype=np.int64)
    nbr[l, h:] = inv


def _rr_bad(nbr, N, D, eye_packed):
    """Ordered pairs at distance > D, counted on bit-packed reachability rows."""
    reach = eye_packed.copy()
    for _ in range(D):
        new = reach.copy()
        for row in nbr:
            new |= reach[row]
        if np.array_equal(new, reach):
            break
        reach = new
    return N * N - int(_POP8[reach].sum())


def _rr_search(d, D, h, rng, deadline):
    """Anneal a d-regular bipartite graph on 2h vertices. Returns (n, edges) with diameter <= D, or None."""
    perms = _rr_init(d, h, rng)
    if perms is None:
        return None
    N = 2 * h
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        _set_layer(nbr, perms[l], h, l)
    eye_packed = np.packbits(np.eye(N, dtype=np.uint8), axis=1)

    cur = _rr_bad(nbr, N, D, eye_packed)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        T = max(0.5, 4.0 * (1.0 - frac))
        l = rng.randrange(d)
        a, a2 = rng.sample(range(h), 2)
        perms[l][a], perms[l][a2] = perms[l][a2], perms[l][a]
        if _clash(perms, d, a) or _clash(perms, d, a2):
            perms[l][a], perms[l][a2] = perms[l][a2], perms[l][a]
            continue
        _set_layer(nbr, perms[l], h, l)
        new = _rr_bad(nbr, N, D, eye_packed)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            perms[l][a], perms[l][a2] = perms[l][a2], perms[l][a]
            _set_layer(nbr, perms[l], h, l)

    if cur != 0:
        return None
    edges = []
    for l in range(d):
        for a in range(h):
            edges.append((a, h + perms[l][a]))
    return N, edges


# ----------------------------------------------------------------------------
# Parent's bi-Cayley lift search over Z_m x| Z_k2, kept as the second route.
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
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
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
        l = rng.randrange(d)
        i = rng.randrange(k)
        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        c2 = _cost(k, G, D, nbr) + _PENALTY * dupcount()
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

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # NEW ROUTE: random regular bipartite graphs with annealing repair.
    # Gets the larger share of the budget when D >= 4 and d >= 3.
    if D >= 4 and d >= 3 and time.monotonic() < deadline:
        now = time.monotonic()
        rr_end = now + 0.65 * (deadline - now)
        h = best_n // 2 + 1
        while time.monotonic() < rr_end:
            now = time.monotonic()
            slice_end = min(rr_end, now + max(3.0, 0.5 * (rr_end - now)))
            res = _rr_search(d, D, h, rng, slice_end)
            if res is None:
                continue
            n_new, e_new = res
            if lib.is_valid(n_new, e_new, d, D):
                consider(n_new, e_new)
                h = max(h + 1, (n_new // 2) + max(1, (n_new // 2) // 400))
            else:
                h = max(d, h - 1)

    # Parent route: bi-Cayley lifts over semidirect products, with a bandit over k.
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
