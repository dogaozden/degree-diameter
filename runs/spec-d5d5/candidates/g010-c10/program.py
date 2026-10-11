import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 8   # groups tried per (base size a, group order m) attempt
LIFT_ITERS = 2500            # annealing steps per (group, base graph) try


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group enumeration.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


# ----------------------------------------------------------------------------
# NEW: multi-orbit voltage lift over a RANDOM d-regular bipartite base multigraph.
#
# Previous search only used a base graph with one A-vertex and one B-vertex.
# Here the base has a A-vertices and a B-vertices, joined by a random
# d-regular bipartite multigraph (a*d darts). Each dart carries a voltage in a
# finite group G of order m, and the lift has 2a*m vertices, all of degree <= d.
#
# Symmetry: left multiplication by G is an automorphism of the lift, so
# diameter <= D holds iff every base vertex's identity lift reaches all
# 2a*m vertices within D steps. Annealing minimises the number of unreached
# (source, vertex) pairs over those 2a sources.
# ----------------------------------------------------------------------------

def _random_base(a, d, rng):
    """Random d-regular bipartite multigraph: A = 0..a-1, B = a..2a-1. Returns darts (u, v)."""
    left = [u for u in range(a) for _ in range(d)]
    right = [v for v in range(a, 2 * a) for _ in range(d)]
    rng.shuffle(right)
    return list(zip(left, right))


def _bad_count(nb, m, T, inc, D):
    """Number of (base source at identity, lift vertex) pairs farther than D apart."""
    size = nb * m
    total = 0
    for s in range(nb):
        seen = bytearray(size)
        src = s * m
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for st in frontier:
                u, x = divmod(st, m)
                row = T[x]
                for tb, h in inc[u]:
                    t = tb * m + row[h]
                    if not seen[t]:
                        seen[t] = 1
                        nxt.append(t)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += size - count
    return total


def _cost(darts, gs, nb, m, T, invs, D):
    """Unreached-pair count of the lift defined by darts with voltages gs."""
    inc = [[] for _ in range(nb)]
    for (u, v), g in zip(darts, gs):
        inc[u].append((v, g))
        inc[v].append((u, invs[g]))
    return _bad_count(nb, m, T, inc, D)


def _anneal_lift(a, d, D, m, T, invs, rng, deadline):
    """Anneal a random base graph's voltages in G (order m) to zero unreached pairs."""
    nb = 2 * a
    darts = _random_base(a, d, rng)
    gs = [rng.randrange(m) for _ in darts]
    cur = _cost(darts, gs, nb, m, T, invs, D)
    for it in range(LIFT_ITERS):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = max(0.5, 3.0 * (1.0 - it / LIFT_ITERS))
        i = rng.randrange(len(gs))
        old = gs[i]
        new = rng.randrange(m)
        if new == old:
            continue
        gs[i] = new
        v = _cost(darts, gs, nb, m, T, invs, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[i] = old
    if cur == 0:
        return darts, gs
    return None


def _try_order(a, m, d, D, rng, deadline):
    """Try groups of order m with base size a; return (n, edges) of a valid-diameter lift, or None."""
    groups = _groups(m)
    rng.shuffle(groups)
    for mm, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(mm, k, r)
        T = [[mul(x, g) for g in range(order)] for x in range(order)]
        invs = [inv(g) for g in range(order)]
        res = _anneal_lift(a, d, D, order, T, invs, rng, deadline)
        if res is not None:
            darts, gs = res
            triples = [(u, v, g) for (u, v), g in zip(darts, gs)]
            return lib.group_lift(2 * a, triples, order, mul)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    A_CHOICES = [1, 2, 3, 4]
    mcur = {a: best[0] // (2 * a) + 1 for a in A_CHOICES}
    budget = 0.4

    while time.monotonic() < deadline:
        progressed = False
        for a in A_CHOICES:
            now = time.monotonic()
            if now >= deadline:
                break
            mcur[a] = max(mcur[a], best[0] // (2 * a) + 1)
            m = mcur[a]
            if 2 * a * m > moore:
                continue
            res = _try_order(a, m, d, D, rng, min(deadline, now + budget))
            if res is not None:
                n, e = res
                consider(n, e)
                mcur[a] = m + 1
                progressed = True
        if all(2 * a * mcur[a] > moore for a in A_CHOICES):
            break
        if not progressed:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
