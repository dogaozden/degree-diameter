import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe base constructions (valid for D = 3 and D >= 4 respectively).
# ----------------------------------------------------------------------------

def _largest_pp(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
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


# ----------------------------------------------------------------------------
# Bold change: bipartite voltage lifts over small (non-cyclic) groups, searched
# by simulated annealing on the number of pairs at distance > D.
#
# Base graph: a A-vertices and a B-vertices, d layers. Layer k is a bijection
# sigma_k: A -> B and each A-vertex i carries a group voltage g_{k,i}. The lift
# has 2*a*|G| vertices, is bipartite, and has max degree <= d. The cost is
# lib.bad_pairs. Cost 0 gives a diameter-D graph (verified with lib.is_valid).
# ----------------------------------------------------------------------------

_GROUP_CACHE = {}


def _groups(order):
    """(m, k, r) describing groups of this order: cyclic (k=1) or Z_m x| Z_k."""
    if order in _GROUP_CACHE:
        return _GROUP_CACHE[order]
    out = []
    for k in range(1, order + 1):
        if order % k:
            continue
        m = order // k
        if k == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    _GROUP_CACHE[order] = out
    return out


def _make_group(m, k, r):
    if k == 1:
        return m, (lambda x, y: (x + y) % m)
    order, mul, _ = lib.semidirect_group(m, k, r)
    return order, mul


def _options(target, d):
    """Lift configurations (a, m, k, r) whose total order 2*a*|G| equals target."""
    half = target // 2
    opts = []
    for a in (1, 2, 3):
        if a > d or half % a:
            continue
        order = half // a
        for (m, k, r) in _groups(order):
            opts.append((a, m, k, r))
    return opts


def _anneal(a, order, mul, d, D, deadline, rng):
    """Search voltages for a diameter-D lift; return (n, edges) if found, else None."""
    sig = []
    for _ in range(d):
        s = list(range(a))
        rng.shuffle(s)
        sig.append(s)
    gv = [[rng.randrange(order) for _ in range(a)] for _ in range(d)]

    def graph(sg, gg):
        darts = [(i, a + sg[k][i], gg[k][i]) for k in range(d) for i in range(a)]
        return lib.group_lift(2 * a, darts, order, mul)

    n, e = graph(sig, gv)
    cost = lib.bad_pairs(n, e, D)
    temp = 0.7
    while cost > 0:
        if time.monotonic() >= deadline:
            return None
        nsig = [list(s) for s in sig]
        ngv = [list(g) for g in gv]
        k = rng.randrange(d)
        i = rng.randrange(a)
        if a > 1 and rng.random() < 0.3:
            j = rng.randrange(a)
            nsig[k][i], nsig[k][j] = nsig[k][j], nsig[k][i]
        else:
            ngv[k][i] = rng.randrange(order)
        nn, ne = graph(nsig, ngv)
        nc = lib.bad_pairs(nn, ne, D)
        if nc <= cost or rng.random() < math.exp(-(nc - cost) / temp):
            sig, gv, cost, n, e = nsig, ngv, nc, nn, ne
    if lib.is_valid(n, e, d, D):
        return n, e
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.85 * time_limit, time_limit - 5.0)
    deadline = start + max(budget, 0.5)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    # Structured fallbacks.
    try:
        if D == 3:
            q = _largest_pp(d - 1)
            if q is not None:
                consider(*lib.projective_plane_incidence(q))
        elif D >= 4:
            q = _largest_pp(d - 1)
            if q is not None:
                consider(*_gq_w(q))
    except Exception:
        pass

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    # Main search: climb the target order, adapting on success and failure.
    target = best[0] + 2
    while time.monotonic() < deadline and target <= moore:
        opts = _options(target, d)
        if not opts:
            target += 2
            continue
        a, m, k, r = rng.choice(opts)
        slice_end = min(deadline, time.monotonic() + 3.0)
        try:
            order, mul = _make_group(m, k, r)
            res = _anneal(a, order, mul, d, D, slice_end, rng)
        except Exception:
            res = None
        if res is not None:
            consider(*res)
            target = max(target, best[0]) + 2
        else:
            target = max(best[0] + 2, target - 2)

    return best
