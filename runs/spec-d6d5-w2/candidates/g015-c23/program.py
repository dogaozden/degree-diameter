import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Algebraic families: projective plane, Araujo-Pardo-Lopez (D = 3) and the
# generalized quadrangle W(q) (D = 4). Used directly, no growth step.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
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
# Bi-Cayley graphs over small groups (the D >= 5 family).
#
# Vertices A_x = x and B_w = G + w. Connection set S (|S| = d, distinct).
# Edge A_x ~ B_{x*s} for x in G, s in S. Left multiplication is an
# automorphism, so the diameter is <= D iff the balls of radius D around
# A_1 and B_1 cover everything. Cost = number of uncovered vertices from
# those two sources; cost 0 means valid.
#
# Search changes from the parent: each group is searched with a tabu walk
# (best of a sampled neighbourhood, with recently removed values forbidden),
# and annealing is kept only as a second attempt on the same group.
# Groups are sampled from a window just above the current best order,
# with a random subset of the candidate specs each round.
# ----------------------------------------------------------------------------

CAP_SPECS = 12


def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def _affine_mul(p):
    """AGL(1, p): element (u-1)*p + b encodes z -> u*z + b with u in 1..p-1."""
    def mul(x, y):
        u, b = divmod(x, p)
        u += 1
        v, c = divmod(y, p)
        v += 1
        return (((u * v) % p) - 1) * p + (u * c + b) % p
    return mul


def _mul_table(order, mul):
    M = np.empty((order, order), dtype=np.int64)
    for x in range(order):
        M[x, :] = [mul(x, y) for y in range(order)]
    return M


def _specs(lo, hi):
    """Group specs with order in [lo, hi] as (order, spec), sorted by order."""
    items = []
    for p in range(3, hi + 2):
        o = p * (p - 1)
        if lo <= o <= hi and _is_prime(p):
            items.append((o, 0, ("aff", p)))
    for m in range(2, hi + 1):
        for k in range(1, hi // m + 1):
            o = m * k
            if o < lo or o > hi:
                continue
            rs = [r for r in range(2, m)
                  if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if rs:
                items.append((o, 1, ("sd", m, k, rs[0])))
                if len(rs) > 2:
                    items.append((o, 1, ("sd", m, k, rs[len(rs) // 2])))
            items.append((o, 2, ("sd", m, k, 1)))
    items.sort(key=lambda t: (t[0], t[1]))
    return [(o, spec) for o, _, spec in items]


def _make_group(spec):
    if spec[0] == "aff":
        p = spec[1]
        o = p * (p - 1)
        return o, _mul_table(o, _affine_mul(p))
    _, m, k, r = spec
    o, mul, _ = lib.semidirect_group(m, k, r)
    return o, _mul_table(o, mul)


def _inverses(M):
    return np.argmax(M == 0, axis=1)


def _adj(M, inv, S, G):
    Sa = np.asarray(S, dtype=np.int64)
    return np.vstack([G + M[:, Sa], M[:, inv[Sa]]])


def _cost(M, inv, S, G, D):
    """Uncovered vertices from A_1 (node 0) and B_1 (node G) within D steps."""
    adj = _adj(M, inv, S, G)
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = adj[frontier].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            frontier = nb
        total += N - int(np.count_nonzero(seen))
    return total


def _tabu(M, inv, G, d, D, deadline, rng, steps=400, cand=40, tenure=8):
    """Tabu walk over connection sets. Returns S with cost 0, or None."""
    S = rng.sample(range(G), d)
    cur = _cost(M, inv, S, G, D)
    tabu = {}
    for it in range(steps):
        if cur == 0 or time.monotonic() >= deadline:
            break
        best_c, best_T, best_mv = None, None, None
        for _ in range(cand):
            i = rng.randrange(d)
            x = rng.randrange(G)
            if x in S or tabu.get((i, x), -1) > it:
                continue
            T = S[:]
            old = T[i]
            T[i] = x
            c = _cost(M, inv, T, G, D)
            if best_c is None or c < best_c:
                best_c, best_T, best_mv = c, T, (i, old)
        if best_T is None:
            continue
        S, cur = best_T, best_c
        tabu[best_mv] = it + tenure
    return S if cur == 0 else None


def _anneal(M, inv, G, d, D, deadline, rng, iters=1500):
    """Simulated annealing restarts over connection sets. Returns S or None."""
    while time.monotonic() < deadline:
        S = rng.sample(range(G), d)
        c = _cost(M, inv, S, G, D)
        T = 2.0
        for _ in range(iters):
            if c == 0 or time.monotonic() >= deadline:
                break
            T = max(0.05, T * 0.997)
            i = rng.randrange(d)
            x = rng.randrange(G)
            if x in S:
                continue
            T2 = S[:]
            T2[i] = x
            c2 = _cost(M, inv, T2, G, D)
            if c2 <= c or rng.random() < math.exp((c - c2) / T):
                S, c = T2, c2
        if c == 0:
            return S
    return None


def _bc_edges(M, S, G):
    E = [(x, G + int(M[x, s])) for x in range(G) for s in S]
    return 2 * G, E


def _bicayley_phase(d, D, floor, deadline, rng, consider, best_fn):
    """Rounds of group sampling just above the current best order, with growing budgets."""
    cache = {}
    rnd = 0
    while time.monotonic() < deadline:
        lo = max(2 * d, best_fn() // 2 + 1, floor)
        window = 24 + 12 * rnd
        specs = _specs(lo, lo + window)
        budget = 1.5 + 0.8 * min(rnd, 6)
        rnd += 1
        if not specs:
            continue
        pool = specs[:max(8, 3 * CAP_SPECS)]
        picks = rng.sample(pool, min(CAP_SPECS, len(pool)))
        picks.sort(key=lambda t: t[0])
        for o, spec in picks:
            if time.monotonic() >= deadline:
                return
            if 2 * o <= best_fn():
                continue
            if spec not in cache:
                if len(cache) > 40:
                    cache.clear()
                try:
                    G, M = _make_group(spec)
                except Exception:
                    continue
                if not np.array_equal(M[0], np.arange(G)):
                    continue
                cache[spec] = (G, M, _inverses(M))
            G, M, inv = cache[spec]
            now = time.monotonic()
            S = _tabu(M, inv, G, d, D, min(deadline, now + budget / 2), rng)
            if S is None:
                S = _anneal(M, inv, G, d, D,
                            min(deadline, time.monotonic() + budget / 2), rng)
            if S is not None:
                n, e = _bc_edges(M, S, G)
                consider(n, e)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.88 * time_limit
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
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D >= 5 and d >= 2:
        moore_half = lib.moore_bound(d, D) // 2
        floor = int(0.4 * moore_half)
        _bicayley_phase(d, D, floor, deadline, rng, consider, lambda: best_n)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
