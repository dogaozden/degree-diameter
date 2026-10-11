"""Voltage-lift search for the diameter-4 bipartite case.

Strategy: start from the incidence graph of the generalized quadrangle W(q) (or the
projective plane for D = 3) as a safe baseline. Then search over bipartite voltage
lifts: a base bipartite multigraph on k + k vertices, each vertex with d darts, and
voltages in a finite group of order N (cyclic or small semidirect products). The lift
has 2*k*N vertices and degree d. Voltages and dart endpoints are improved by hill
climbing on lib.bad_pairs (plateau moves allowed). Each success raises the target
order, and every returned graph is re-verified with lib.is_valid.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline: generalized quadrangle W(q) incidence graph (diameter 4).
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


def _pg_best(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group options for voltage lifts.
# ----------------------------------------------------------------------------

def _group_options(N):
    """Return up to three (order, mul) pairs of groups of order N: cyclic and small semidirect products."""
    opts = [tuple(lib.cyclic_group(N)[:2])]
    for a in range(3, N):
        if N % a or N // a < 2:
            continue
        b = N // a
        for r in range(2, a):
            if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a:
                opts.append(tuple(lib.semidirect_group(a, b, r)[:2]))
                break
    return opts[:3]


# ----------------------------------------------------------------------------
# Lift search state: k A-vertices and k B-vertices, each with d darts.
# ----------------------------------------------------------------------------

def _new_state(k, order, mul, d, D, rng):
    A = [u for u in range(k) for _ in range(d)]
    B = [k + u for u in range(k) for _ in range(d)]
    rng.shuffle(B)
    darts = [[A[i], B[i], rng.randrange(order)] for i in range(len(A))]
    n, e = lib.group_lift(2 * k, darts, order, mul)
    return {"k": k, "order": order, "mul": mul, "darts": darts,
            "n": n, "edges": e, "bad": lib.bad_pairs(n, e, D), "dead": False}


def _step(st, D, rng, until):
    """Hill-climb on bad pairs until zero or the time limit. Returns True if the lift has diameter <= D."""
    k, order, mul = st["k"], st["order"], st["mul"]
    while st["bad"] > 0 and time.monotonic() < until:
        cand = [t[:] for t in st["darts"]]
        i = rng.randrange(len(cand))
        if rng.random() < 0.5:
            cand[i][2] = rng.randrange(order)
        else:
            j = rng.randrange(len(cand))
            if cand[i][1] == cand[j][1]:
                continue
            cand[i][1], cand[j][1] = cand[j][1], cand[i][1]
        n2, e2 = lib.group_lift(2 * k, cand, order, mul)
        b2 = lib.bad_pairs(n2, e2, D)
        if b2 <= st["bad"]:
            st.update(darts=cand, n=n2, edges=e2, bad=b2)
    return st["bad"] == 0


def _states(best_n, moore, d, D, rng):
    out = []
    for k in (2, 3, 4):
        lo = best_n // (2 * k) + 1
        for N in (lo, lo + 1):
            if 2 * k * N > moore:
                continue
            for order, mul in _group_options(N):
                out.append(_new_state(k, order, mul, d, D, rng))
    return out


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.75 * time_limit, time_limit - 8.0)
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

    moore = lib.moore_bound(d, D)

    if D == 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(*pg)
    elif D >= 4:
        for q in range(min(d - 1, 9), 1, -1):
            if lib.is_prime_power(q):
                consider(*_gq_w(q))
                break

    # Calibration shortcut: already at the Moore bound.
    if best[0] >= moore:
        return best

    try:
        states = _states(best[0], moore, d, D, rng)
        while time.monotonic() < deadline and states:
            if all(st["dead"] for st in states):
                break
            for st in list(states):
                if time.monotonic() >= deadline:
                    break
                if st["dead"]:
                    continue
                ok = _step(st, D, rng, min(deadline, time.monotonic() + 0.8))
                if ok:
                    if st["n"] > best[0] and lib.is_valid(st["n"], st["edges"], d, D):
                        best = (st["n"], st["edges"])
                        if best[0] >= moore:
                            return best
                        states = _states(best[0], moore, d, D, rng)
                        break
                    st["dead"] = True
    except Exception:
        pass

    return best
