import itertools
import random
import time
from math import gcd

import lib


def _largest_pp(x):
    """Largest prime power <= x, or None."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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
            for s in range(q):
                for t in range(q):
                    if s == 0 and t == 0:
                        continue
                    v = tuple(F.add(F.mul(s, x[k]), F.mul(t, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


# ----------------------------------------------------------------------------
# Voltage lifts over small groups: bipartite base with a A-vertices and a
# B-vertices, d darts at each vertex (a sum of d random permutation matrices),
# each dart carrying a random group element. Search by hill climbing on the
# number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _perm_darts(a, d, rng):
    """Dart endpoints (u, v): every A-vertex and every B-vertex gets exactly d darts."""
    darts = []
    for _ in range(d):
        p = list(range(a))
        rng.shuffle(p)
        for u in range(a):
            darts.append((u, p[u]))
    return darts


def _sample_group(n_lo, rng):
    """Random group (order, mul, inv) with order >= n_lo, drawn from semidirect products Z_m x| Z_k."""
    for _ in range(60):
        k = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8])
        m_lo = -(-n_lo // k)
        m = rng.randint(m_lo, m_lo + max(2, m_lo // 3))
        if m < 2:
            continue
        if k == 1:
            return lib.semidirect_group(m, 1, 1)
        rs = [r for r in range(1, m) if gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if rs:
            return lib.semidirect_group(m, k, rng.choice(rs))
    return None


def _build_lift(a, uv, gs, order, mul):
    """Lift: A-block vertices 0..a-1, B-block vertices a..2a-1."""
    darts = [(u, a + v, g) for (u, v), g in zip(uv, gs)]
    return lib.group_lift(2 * a, darts, order, mul)


def _lift_search(d, D, best_n, deadline, rng, steps=400):
    """Random restarts with hill climbing; returns the first verified lift larger than best_n, or None."""
    while time.monotonic() < deadline:
        a = rng.choice([1, 2, 2, 3, 3, 4])
        n_lo = best_n // (2 * a) + 1
        grp = _sample_group(n_lo, rng)
        if grp is None:
            continue
        order, mul, _ = grp
        uv = _perm_darts(a, d, rng)
        gs = [rng.randrange(order) for _ in uv]
        n, edges = _build_lift(a, uv, gs, order, mul)
        cur = lib.bad_pairs(n, edges, D)
        it = 0
        while cur > 0 and it < steps and time.monotonic() < deadline:
            j = rng.randrange(len(gs))
            old = gs[j]
            gs[j] = rng.randrange(order)
            n2, e2 = _build_lift(a, uv, gs, order, mul)
            c2 = lib.bad_pairs(n2, e2, D)
            if c2 <= cur:
                cur = c2
            else:
                gs[j] = old
            it += 1
        if cur == 0:
            n, edges = _build_lift(a, uv, gs, order, mul)
            if n > best_n and lib.is_valid(n, edges, d, D):
                return n, edges
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        q = _largest_pp(d - 1)
        if q is not None:
            consider(*lib.projective_plane_incidence(q))
    elif D >= 4:
        q = _largest_pp(min(d - 1, 8))
        if q is not None and time.monotonic() < deadline:
            consider(*_gq_w(q))

    if best[0] >= lib.moore_bound(d, D):
        return best

    while time.monotonic() < deadline:
        res = _lift_search(d, D, best[0], deadline, rng)
        if res is None:
            break
        best = res

    return best
