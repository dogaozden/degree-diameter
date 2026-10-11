import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4, degree q + 1).
# ----------------------------------------------------------------------------

def _gq_w(q):
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
# New construction: random-regular bipartite base over a finite group, lifted
# (lib.group_lift). Hill-climb on the number of pairs at distance > D.
#
# Base: k vertices on side A, k on side B, d "rounds". Round r is a permutation
# sigma_r of the B-indices (so every vertex has base degree d) with a group
# label h[r][i] per dart. Lift order = 2 * k * |G|.
# ----------------------------------------------------------------------------

def _groups(g, rng):
    """Return multiplication functions for Z_g and for some semidirect products of order g."""
    out = [lib.cyclic_group(g)[1]]
    for kk in range(2, g):
        if g % kk:
            continue
        m = g // kk
        if m < 2:
            continue
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m]
        if rs:
            out.append(lib.semidirect_group(m, kk, rng.choice(rs))[1])
    return out


def _climb(k, d, D, g, mul, end, rng):
    """Hill-climb a lifted base graph until every pair is within distance D, or time runs out."""
    sig = [rng.sample(range(k), k) for _ in range(d)]
    hh = [[rng.randrange(g) for _ in range(k)] for _ in range(d)]

    def make():
        darts = [(i, k + sig[r][i], hh[r][i]) for r in range(d) for i in range(k)]
        return lib.group_lift(2 * k, darts, g, mul)

    n_, e_ = make()
    cur = lib.bad_pairs(n_, e_, D)
    while cur > 0 and time.monotonic() < end:
        r = rng.randrange(d)
        if rng.random() < 0.6:
            i = rng.randrange(k)
            old = hh[r][i]
            hh[r][i] = rng.randrange(g)
            undo = ("h", i, old)
        else:
            i1, i2 = rng.sample(range(k), 2)
            sig[r][i1], sig[r][i2] = sig[r][i2], sig[r][i1]
            undo = ("s", i1, i2)
        n2, e2 = make()
        val = lib.bad_pairs(n2, e2, D)
        if val <= cur or rng.random() < 0.003:
            cur = val
            n_, e_ = n2, e2
        else:
            if undo[0] == "h":
                hh[r][undo[1]] = undo[2]
            else:
                i1, i2 = undo[1], undo[2]
                sig[r][i1], sig[r][i2] = sig[r][i2], sig[r][i1]
    return (n_, e_) if cur == 0 else None


def _lift_search(d, D, deadline, rng, best, consider):
    ks = [2, 3, 4, 5, 6]
    while time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        slice_len = max(3.0, min(10.0, remaining / 6.0))
        k = rng.choice(ks)
        best_n = best[0]
        g = -(-(best_n + 1) // (2 * k)) + rng.choice([0, 0, 1])
        g = max(g, 2)
        mul = rng.choice(_groups(g, rng))
        end = min(deadline, time.monotonic() + slice_len)
        res = _climb(k, d, D, g, mul, end, rng)
        if res is not None:
            consider(res[0], res[1])
            best = (res[0], res[1]) if res[0] > best_n and lib.is_valid(res[0], res[1], d, D) else best
    return best


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + max(0.3 * T, min(0.8 * T, T - 6.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best
    if d == 2:
        # Even cycle C_{2D}: bipartite, degree 2, diameter D.
        consider(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])
        return best

    # Known optimal constructions where available.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best
    if D == 4 and lib.is_prime_power(d - 1):
        try:
            consider(*_gq_w(d - 1))
        except Exception:
            pass
        return best

    if best[0] >= lib.moore_bound(d, D):
        return best

    # Strong-ish bases to start the lift search from.
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4:
        q = next((q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)), None)
        if q is not None:
            try:
                consider(*_gq_w(q))
            except Exception:
                pass

    # New construction: group-lift search with hill-climbing.
    if time.monotonic() < deadline and best[0] >= 2:
        try:
            best = _lift_search(d, D, deadline, rng, best, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
