import itertools
import math
import random
import time

import lib

MAX_GROUPS = 6        # groups tried per (p, N) attempt
ITERS = 1200          # annealing steps per try
T_HOT = 1.5           # initial annealing temperature (unreached-pair units)
T_COLD = 0.15         # final annealing temperature
LO_FRAC = 0.47        # lift search starts at this fraction of the Moore bound
BUDGET0 = 0.25        # initial time budget per (p, N) attempt, doubled per fruitless pass


# ----------------------------------------------------------------------------
# Baseline families (fast, validated before use).
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
# NEW: multi-orbit voltage lifts with a random base matrix.
#
# The base graph is bipartite with p vertices A_0..A_{p-1} and p vertices
# B_0..B_{p-1}. Its multigraph is a sum of d random permutation matrices, so every
# base vertex has degree d. Each base dart (i, j) carries a voltage g in a group G
# of order N. The lift has vertices (side, orbit, x), x in G, and edges
#     A_{i,x} -- B_{j, x*g}   for every dart (i, j, g).
# Darts in the same cell (i, j) need distinct voltages, which keeps the lift simple.
# Left multiplication by G is an automorphism that is transitive on each orbit,
# so the diameter is at most D iff every one of the 2p orbit representatives
# (identity elements) reaches all vertices within D steps.
# Multi-orbit lifts (p = 2, 3) reach orders that single-orbit bi-Cayley graphs miss.
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


def _random_cells(p, d, rng):
    """Base darts: a sum of d random permutations of range(p), so each row and column sums to d."""
    cells = []
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        for i in range(p):
            cells.append((i, perm[i]))
    return cells


def _unreached_lift(N, p, T, cells, gs, D, sources):
    """Total count of (source, vertex) pairs not within distance D, over all orbit representatives."""
    V = 2 * p * N
    adj = [[] for _ in range(V)]
    for k, (i, j) in enumerate(cells):
        g = gs[k]
        base_b = (p + j) * N
        base_a = i * N
        for x in range(N):
            a = base_a + x
            b = base_b + T[x][g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal_lift(N, p, d, D, cells, T, rng, iters, deadline):
    """Anneal the voltages on the darts so that the lift has diameter <= D."""
    K = len(cells)
    sources = [i * N for i in range(p)] + [(p + j) * N for j in range(p)]
    used = [set() for _ in range(p * p)]
    gs = [0] * K
    for k, (i, j) in enumerate(cells):
        c = i * p + j
        g = rng.randrange(N)
        while g in used[c]:
            g = rng.randrange(N)
        gs[k] = g
        used[c].add(g)
    cur = _unreached_lift(N, p, T, cells, gs, D, sources)
    for it in range(iters):
        if cur == 0:
            return gs
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        k = rng.randrange(K)
        i, j = cells[k]
        c = i * p + j
        g_new = rng.randrange(N)
        if g_new in used[c]:
            continue
        gs2 = gs[:]
        gs2[k] = g_new
        v = _unreached_lift(N, p, T, cells, gs2, D, sources)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            used[c].discard(gs[k])
            used[c].add(g_new)
            gs, cur = gs2, v
    if cur == 0:
        return gs
    return None


def _attempt(N, p, d, D, rng, att_deadline):
    """Try groups of order N with a random base matrix for p orbits per side."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > att_deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        cells = _random_cells(p, d, rng)
        gs = _anneal_lift(N, p, d, D, cells, T, rng, ITERS, att_deadline)
        if gs is not None:
            return T, cells, gs
    return None


def _lift_edges(N, p, T, cells, gs):
    """Expand a found voltage assignment into the explicit edge list."""
    edges = []
    for k, (i, j) in enumerate(cells):
        g = gs[k]
        for x in range(N):
            edges.append((i * N + x, (p + j) * N + T[x][g]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

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
    lo = max(best_n + 1, int(LO_FRAC * moore))
    cands = sorted({(2 * p * N, p, N)
                    for p in (2, 1, 3)
                    for N in range(max(d, 2), moore // (2 * p) + 1)
                    if lo <= 2 * p * N <= moore})

    budget = BUDGET0
    while time.monotonic() < deadline:
        remaining = [c for c in cands if c[0] > best_n]
        if not remaining:
            break
        success = False
        for cnt, p, N in remaining:
            now = time.monotonic()
            if now >= deadline:
                break
            if cnt <= best_n:
                continue
            att_deadline = min(deadline, now + budget)
            res = _attempt(N, p, d, D, rng, att_deadline)
            if res is None:
                continue
            T, cells, gs = res
            consider(2 * p * N, _lift_edges(N, p, T, cells, gs))
            success = True
        if not success:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
