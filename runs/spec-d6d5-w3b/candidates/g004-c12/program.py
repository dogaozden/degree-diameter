import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Base families.
#   D = 3: incidence graph of PG(2, q).
#   D = 4: incidence graph of the generalized quadrangle W(q), diameter 4.
#   D >= 5: cyclic voltage lifts of W(q), searched by annealing with a
#           bit-parallel reachability cost. A lift of order m * 2(q+1)(q^2+1)
#           has diameter <= D iff every base vertex reaches all vertices in D
#           steps (Z_m acts freely, so only the m-indexed representatives matter).
# A validated fallback (K_{d,d} or a base incidence graph) is always kept.
# ----------------------------------------------------------------------------


def _pick_q(d, cap):
    """Largest prime power q with q + 1 <= d and q <= cap, or None."""
    for q in range(min(d - 1, cap), 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _gq_w(q):
    """Incidence graph of points and lines of W(q). Returns (n, edges, P) or None.

    Points are 0..P-1, lines are P..2P-1. Degree is q + 1 everywhere.
    """
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

    lines = set()
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
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
            if len(L) == q + 1:
                lines.add(frozenset(L))
    lines = sorted(sorted(L) for L in lines)
    if len(lines) != (q + 1) * (q * q + 1):
        return None
    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges, P


def _lift_search(n0, base_edges, deg, D, m, deadline, rng):
    """Anneal Z_m voltages on a simple regular bipartite base so the lift has diameter <= D.

    Base vertices 0..P-1 are points and P..n0-1 are lines; the dart (u, v) gets a voltage a
    and joins (u, g) to (v, g + a). Returns (n, edges) or None.
    """
    E = len(base_edges)
    N = n0 * m

    pa = [0] * E
    pb = [0] * E
    cnt = [0] * n0
    for e, (u, v) in enumerate(base_edges):
        pa[e] = cnt[u]
        cnt[u] += 1
        pb[e] = cnt[v]
        cnt[v] += 1
    if min(cnt) != deg or max(cnt) != deg:
        return None

    nb = np.zeros((N, deg), dtype=np.int64)
    volt = [rng.randrange(m) for _ in range(E)]
    ar = np.arange(m, dtype=np.int64)

    def set_dart(e):
        u, v = base_edges[e]
        a = volt[e]
        nb[u * m + ar, pa[e]] = v * m + (ar + a) % m
        nb[v * m + ar, pb[e]] = u * m + (ar - a) % m

    for e in range(E):
        set_dart(e)

    W = (n0 + 63) // 64
    R0 = np.zeros((N, W), dtype=np.uint64)
    for r in range(n0):
        R0[r * m, r // 64] |= np.uint64(1 << (r % 64))

    def cost():
        S = R0
        for _ in range(D):
            S = S | np.bitwise_or.reduce(S[nb], axis=1)
        return N * n0 - int(np.unpackbits(S.view(np.uint8)).sum())

    cur = cost()
    T = 3.0
    it = 0
    while cur > 0 and time.monotonic() < deadline:
        it += 1
        e = rng.randrange(E)
        old = volt[e]
        new = rng.randrange(m - 1)
        if new >= old:
            new += 1
        volt[e] = new
        set_dart(e)
        c = cost()
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
        else:
            volt[e] = old
            set_dart(e)
        if it % 200 == 0:
            T = max(0.3, T * 0.95)

    if cur != 0:
        return None
    edges = []
    for e, (u, v) in enumerate(base_edges):
        a = volt[e]
        for g in range(m):
            edges.append((u * m + g, v * m + (g + a) % m))
    return N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit

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

    if D >= 3:
        q = _pick_q(d, 23)
        if q is not None:
            n, e = lib.projective_plane_incidence(q)
            consider(n, e)

    if D >= 4:
        q = _pick_q(d, 7)
        if q is not None:
            g = _gq_w(q)
            if g is not None:
                n, e, _P = g
                consider(n, e)

                if D >= 5:
                    # Lift search over the generalized quadrangle base (degree q + 1 <= d).
                    rng = random.Random(seed * 1000003 + d * 101 + D)
                    deg = q + 1
                    achieved = False
                    for m, frac in ((3, 0.5), (4, 0.7), (5, 0.8)):
                        now = time.monotonic()
                        if now >= deadline:
                            break
                        dl = now + frac * (deadline - now)
                        res = _lift_search(n, e, deg, D, m, dl, rng)
                        if res is None:
                            break
                        consider(res[0], res[1])
                        achieved = True
                    if not achieved and time.monotonic() < deadline:
                        res = _lift_search(n, e, deg, D, 2, deadline, rng)
                        if res is not None:
                            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
