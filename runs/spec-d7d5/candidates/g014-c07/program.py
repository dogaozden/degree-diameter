import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / structured baselines (kept from the parent for safety).
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
# Bold change: single-base bi-Cayley graphs over a group G of exact order N/2,
# searched by a time-based annealing that moves ONE connection element at a time.
#
# Vertices: A_g = g (0 <= g < G), B_h = G + h.
# Connection set S = {s_1..s_d} (distinct). Edges A_g -- B_{g*s} for s in S.
# Left multiplication is an automorphism, so distances from A_e and B_e
# determine the whole diameter. Cost = number of (representative, vertex)
# pairs not reached within D steps (0 means diameter <= D).
#
# Group families: Z_m x|_r Z_k2 (r = 1 gives the direct/cyclic product), with
# k2 ranging over divisors of G. Ladder search: target order just above the
# current best, with fresh groups and fresh connection sets each attempt.
# ----------------------------------------------------------------------------

_POP2 = np.array([0, 1, 1, 2], dtype=np.int64)
_ATTEMPT_MIN = 2.0


def _divisors_small(G):
    return [k for k in range(1, min(G, 40) + 1) if G % k == 0]


def _sample_group(G, rng):
    """Random group of exact order G as (MUL, INV) tables; element index a*k2+b."""
    ks = _divisors_small(G)
    k2 = rng.choice(ks)
    m = G // k2
    r = 1
    if k2 > 1 and m > 2:
        for _ in range(80):
            c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    MUL = ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    rows, cols = np.nonzero(MUL == 0)
    INV = np.empty(G, dtype=np.int64)
    INV[rows] = cols
    return MUL, INV


def _cost(nbr, G, D):
    """Unreached (representative, vertex) pairs; representatives are A_e (index 0) and B_e (index G)."""
    N = 2 * G
    reach = np.zeros(N, dtype=np.int64)
    reach[0] = 1
    reach[G] = 2
    for _ in range(D):
        new = reach.copy()
        for row in nbr:
            new |= reach[row]
        if np.array_equal(new, reach):
            break
        reach = new
    return 2 * N - int(_POP2[reach].sum())


def _attempt(G, d, D, rng, deadline):
    """Anneal a connection set of size d in a random group of order G. Returns (n, edges) or None."""
    MUL, INV = _sample_group(G, rng)
    N = 2 * G
    ar = np.arange(G)

    def set_row(nbr, l, s):
        nbr[l, :G] = G + MUL[:, s]           # A_g -- B_{g*s}
        nbr[l, G:] = MUL[ar, INV[s]]         # B_h -- A_{h*s^-1}

    S = rng.sample(range(G), d)
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        set_row(nbr, l, S[l])
    cost = _cost(nbr, G, D)
    c0 = float(max(cost, 1))
    T0 = max(1.0, 0.03 * c0)
    start = time.monotonic()
    span = max(1e-3, deadline - start)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - start) / span
        T = T0 * (1.0 - frac) + 0.15
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        set_row(nbr, i, x)
        c2 = _cost(nbr, G, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            S[i] = old
            set_row(nbr, i, old)

    if cost != 0:
        return None
    edges = [(u, int(nbr[l, u])) for u in range(G) for l in range(d)]
    return N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
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

    if D == 2:
        return best

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

    # Ladder search: target group order just above the current best half-order.
    attempt_cap = max(_ATTEMPT_MIN, budget / 6.0)
    while True:
        now = time.monotonic()
        if deadline - now < 0.3:
            break
        lo = best_n // 2
        G = lo + 1 + rng.randrange(2)
        if G < d + 1:
            G = d + 1
        res = _attempt(G, d, D, rng, min(deadline, now + attempt_cap))
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
