import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Seed: incidence graph of the generalized quadrangle W(q), diameter 4.
# Returns (P, edges, number_of_lines); points are A-side 0..P-1, lines B-side.
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
    E = [(p, j) for j, L in enumerate(lines) for p in L]
    return P, E, len(lines)


# ----------------------------------------------------------------------------
# Bipartite switch annealing with bad-pair cost.
#
# A graph is (m, E): A-vertices 0..m-1, B-vertices 0..m-1, edge (a, b) joins
# A-vertex a to B-vertex b. Combined label of B-vertex b is m + b.
# Degrees stay within d throughout: switches preserve degrees and growth
# only adds edges at two fresh vertices.
# ----------------------------------------------------------------------------

def _bad_pairs(m, E, D):
    """Number of ordered vertex pairs at distance greater than D (0 means valid)."""
    n = 2 * m
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(m + b)
        adj[m + b].append(a)
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        if new == ball:
            break
        ball = new
    return sum(n - b.bit_count() for b in ball)


def _anneal(m, E, Eset, D, rng, iters, deadline):
    """Simulated annealing over degree-preserving edge switches; returns (cost, E, Eset)."""
    E = list(E)
    Eset = set(Eset)
    c = _bad_pairs(m, E, D)
    if c == 0 or len(E) < 2:
        return c, E, Eset
    T0 = max(1.0, 0.05 * c)
    T1 = 0.3
    decay = (T1 / T0) ** (1.0 / iters) if T0 > T1 else 1.0
    T = T0
    for _ in range(iters):
        if time.monotonic() > deadline:
            break
        T *= decay
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a, b = E[i]
        c2, d2 = E[j]
        if a == c2 or b == d2:
            continue
        e1 = (a, d2)
        e2 = (c2, b)
        if e1 in Eset or e2 in Eset:
            continue
        E[i] = e1
        E[j] = e2
        Eset.discard((a, b))
        Eset.discard((c2, d2))
        Eset.add(e1)
        Eset.add(e2)
        nc = _bad_pairs(m, E, D)
        delta = nc - c
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            c = nc
            if c == 0:
                break
        else:
            E[i] = (a, b)
            E[j] = (c2, d2)
            Eset.discard(e1)
            Eset.discard(e2)
            Eset.add((a, b))
            Eset.add((c2, d2))
    return c, E, Eset


def _grow(m, E, d, rng):
    """Add one A-vertex and one B-vertex: remove a d-matching and rewire it through them."""
    pick = None
    for _ in range(60):
        order = E[:]
        rng.shuffle(order)
        usedA, usedB, cand = set(), set(), []
        for a, b in order:
            if a not in usedA and b not in usedB:
                cand.append((a, b))
                usedA.add(a)
                usedB.add(b)
                if len(cand) == d:
                    break
        if len(cand) == d:
            pick = cand
            break
    if pick is None:
        return None
    removed = set(pick)
    E2 = [e for e in E if e not in removed]
    S2 = set(E2)
    for a, b in pick:
        E2.append((m, b))
        E2.append((a, m))
        S2.add((m, b))
        S2.add((a, m))
    return m + 1, E2, S2


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fast path: projective plane meets the Moore bound (d = q + 1, D = 3).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    fallback = (2 * d, [(i, d + j) for i in range(d) for j in range(d)])
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    rng = random.Random(seed * 1000003 + 97 * d + D)

    # Starting point: K_{d,d}, or a larger valid GQ incidence graph when D >= 4.
    m = d
    E = [(i, j) for i in range(d) for j in range(d)]
    if D >= 4 and 2 <= d - 1 <= 7 and lib.is_prime_power(d - 1):
        P, E0, nl = _gq_w(d - 1)
        if nl == P and lib.is_valid(2 * P, [(a, P + b) for a, b in E0], d, D):
            m, E = P, E0

    limit = lib.moore_bound(d, D) // 2
    Eset = set(E)
    while m < limit and time.monotonic() < deadline:
        success = False
        for _ in range(3):
            if time.monotonic() >= deadline:
                break
            g = _grow(m, E, d, rng)
            if g is None:
                continue
            m2, E2, S2 = g
            c, E3, S3 = _anneal(m2, E2, S2, D, rng, 3000, deadline)
            if c == 0:
                m, E, Eset = m2, E3, S3
                success = True
                break
        if not success:
            break

    n = 2 * m
    edges = [(a, m + b) for a, b in E]
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return fallback
