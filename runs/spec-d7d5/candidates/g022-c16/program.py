import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact and generalized-polygon fallbacks (unchanged from the safe baseline).
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
# New main construction: abelian bi-Cayley (Haar-type) graphs.
#
# Vertices A_g = g and B_h = G + h for g, h in an abelian group G of order M.
# Connection set S (|S| = d, distinct) gives edges A_g ~ B_{g+s}.
# This is d-regular and bipartite. Translations and the side-swapping map
# A_g <-> B_{-g} are automorphisms, so diameter <= D holds iff every vertex is
# within distance D of A_0. We search over S by simulated annealing, minimising
# the number of vertices unreached from A_0 with a fast boolean BFS.
#
# Unlike the parent's non-abelian semidirect lifts, this family uses abelian
# groups Z_a x Z_b (including cyclic Z_M) with a single base pair of sides.
# ----------------------------------------------------------------------------

def _abelian(a, b):
    """Z_a x Z_b, element (x, y) coded as x*b + y. Returns (order, add_table)."""
    G = a * b
    x = np.arange(G, dtype=np.int64) // b
    y = np.arange(G, dtype=np.int64) % b
    add = (((x[:, None] + x[None, :]) % a) * b + (y[:, None] + y[None, :]) % b).astype(np.int64)
    return G, add


def _random_group(M, rng):
    """Return (a, b) with Z_a x Z_b of order M; cyclic is common."""
    divs = [a for a in range(1, M + 1) if M % a == 0 and a * a <= M]
    if rng.random() < 0.4:
        return 1, M
    a = rng.choice(divs)
    return a, M // a


def _unreached(G, add, neg, S, D):
    """Number of vertices (over both sides) not within distance D of A_0."""
    S = np.asarray(S, dtype=np.int64)
    addS = add[:, S].T           # addS[i, g] = g + S[i]
    subS = add[:, neg[S]].T      # subS[i, h] = h - S[i]
    visA = np.zeros(G, dtype=bool)
    visA[0] = True
    visB = np.zeros(G, dtype=bool)
    fa = visA.copy()
    fb = np.zeros(G, dtype=bool)
    for step in range(D):
        if step % 2 == 0:
            nb = fa[subS].any(axis=0) & ~visB
            visB |= nb
            fb = nb
        else:
            na = fb[addS].any(axis=0) & ~visA
            visA |= na
            fa = na
        if visA.all() and visB.all():
            break
    return int(2 * G - visA.sum() - visB.sum())


def _search(G, add, neg, d, D, rng, deadline, iters, patience):
    """Simulated annealing over connection sets S. Returns S with full coverage, or None."""
    S = rng.sample(range(G), d)
    cost = _unreached(G, add, neg, S, D)
    best_cost = cost
    last = 0
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last > patience:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _unreached(G, add, neg, S2, D)
        temp = max(0.5, 3.0 * (1.0 - t / iters))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            S, cost = S2, c2
            if cost < best_cost:
                best_cost, last = cost, t
    return S if cost == 0 else None


def _edges(G, add, S):
    """Build (2G, edges) for the bi-Cayley graph with connection set S."""
    edges = []
    for s in S:
        col = add[:, s]
        for g in range(G):
            edges.append((g, G + int(col[g])))
    return 2 * G, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, time_limit - 6.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    # Exact constructions (calibration-style cases return immediately).
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

    if D < 3:
        return best

    # Main search: climb a ladder of abelian group orders M just above the
    # current best half-order, with random small offsets to diversify groups.
    while time.monotonic() < deadline:
        M = best[0] // 2 + 1 + rng.randrange(0, 4)
        if M <= d:
            continue
        a, b = _random_group(M, rng)
        G, add = _abelian(a, b)
        neg = np.argmax(add == 0, axis=1)
        S = _search(G, add, neg, d, D, rng, deadline, 6000, 1500)
        if S is not None:
            n, e = _edges(G, add, S)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
