import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (always available as fallbacks).
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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2, searched by greedy
# coordinate descent with iterated-local-search perturbations.
# (Different search dynamics from the earlier annealing: each slot is set to
# the best voltage among a random candidate sample, given all other slots.)
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4, 5)
_CAND = 48


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
    """Write layer l's neighbours for A-block i and B-block j with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex over block representatives within distance D."""
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
    """Number of unreached (representative, vertex) pairs; zero iff the lift has diameter <= D."""
    return 2 * k * N - int(_POP[reach].sum())


def _lift_search(d, D, k, G, Ts, Invs, rng, deadline):
    """Greedy coordinate descent with perturbation. Returns (n, edges) or None."""
    N = 2 * k * G
    layers = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        layers.append(p)
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)

    def put(l, i):
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    for l in range(d):
        for i in range(k):
            put(l, i)

    def cost():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        dup = len(keys) - len(set(keys))
        return _unreached(k, N, _reach(k, G, D, nbr, d)) + _PENALTY * dup

    slots = [(l, i) for l in range(d) for i in range(k)]
    cur = cost()
    best_cost = cur
    best_S = [row[:] for row in S]
    stall = 0

    while cur > 0 and time.monotonic() < deadline:
        rng.shuffle(slots)
        improved = False
        for l, i in slots:
            if time.monotonic() > deadline:
                break
            old = S[l][i]
            bv, bs = cur, old
            for s in rng.sample(range(G), min(G, _CAND)):
                if s == old:
                    continue
                S[l][i] = s
                put(l, i)
                c = cost()
                if c < bv:
                    bv, bs = c, s
            S[l][i] = bs
            put(l, i)
            if bs != old:
                improved = True
            cur = bv
            if cur == 0:
                break

        if cur < best_cost:
            best_cost = cur
            best_S = [row[:] for row in S]

        stall = 0 if improved else stall + 1
        if cur > 0 and stall >= 2 and time.monotonic() < deadline:
            # Iterated local search: restart from the best state with a small kick.
            for l in range(d):
                S[l][:] = best_S[l]
            for _ in range(rng.randint(2, 4)):
                S[rng.randrange(d)][rng.randrange(k)] = rng.randrange(G)
            for l in range(d):
                for i in range(k):
                    put(l, i)
            cur = cost()
            stall = 0

    if cur != 0:
        return None
    edges = []
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.append((u, int(v)))
    return N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    search_deadline = start + max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle C_{2D}: bipartite, 2-regular, diameter D.
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best

    if D == 4 and time.monotonic() < search_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: bi-Cayley lifts over semidirect products with several block counts.
    span = search_deadline - start
    attempt = max(4.0, 0.3 * span)
    while time.monotonic() < search_deadline - 1.0:
        k = rng.choice(_KS)
        need = best_n // (2 * k) + 1
        target = need + rng.randrange(0, max(2, need // 50 + 1))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G_order = m * k2
        if 2 * k * G_order <= best_n or 2 * k * G_order > best_n * 1.08:
            continue
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        res = _lift_search(d, D, k, G, Ts, Invs, rng,
                           min(search_deadline, time.monotonic() + attempt))
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
