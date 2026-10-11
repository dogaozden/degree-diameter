import itertools
import math
import random
import time

import lib

ITERS = 600                 # annealing steps per (group, base pattern) try
GROUPS_PER_TRY = 40         # groups tried per attempt
A_CYCLE = (2, 3, 4, 2, 3, 1)  # number of base orbits per side, tried in rotation


# ----------------------------------------------------------------------------
# Baseline families (fast, always validated before use).
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
# Groups: semidirect products Z_m x|_r Z_k of order N (identity coded as 0).
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
# NEW: multi-orbit voltage lift.
#
# Base: a A-vertices and a B-vertices, with a d-regular bipartite multigraph
# pattern M (row and column sums d) given as a sum of d random permutations.
# Each base dart (i, j) carries a voltage g in G, with distinct voltages for
# the same (i, j). Lift vertices: A(i, x) = i*N + x, B(j, y) = aN + j*N + y.
# Edge A(i, x) -- B(j, x*g) for each dart (i, j, g).
#
# Left multiplication by h is an automorphism, so each orbit has one
# eccentricity. Diameter needs BFS only from the 2a orbit identities A(i,1),
# B(j,1). The graph has 2aN vertices and degree d.
# ----------------------------------------------------------------------------

def _random_pattern(a, d, rng):
    """Multiplicity matrix with row and column sums d, as a sum of d random permutations."""
    M = [[0] * a for _ in range(a)]
    for _ in range(d):
        perm = list(range(a))
        rng.shuffle(perm)
        for i in range(a):
            M[i][perm[i]] += 1
    return M


def _cost(a, N, T, ginv, pairs, gs, D):
    """Total number of (source, vertex) pairs not within distance D over the 2a orbit sources."""
    adjA = [[] for _ in range(a)]
    adjB = [[] for _ in range(a)]
    for (i, j), g in zip(pairs, gs):
        adjA[i].append((j, g))
        adjB[j].append((i, ginv[g]))
    aN = a * N
    V = 2 * aN
    total = 0
    sources = list(range(0, aN, N)) + list(range(aN, V, N))
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < aN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in adjA[i]:
                        v = aN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - aN, N)
                    row = T[y]
                    for i, h in adjB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(a, N, T, ginv, pairs, D, rng, iters, deadline):
    """Anneal voltages so that the lift has diameter <= D; return voltage list or None."""
    K = len(pairs)
    members = {}
    for k, key in enumerate(pairs):
        members.setdefault(key, []).append(k)
    gs = [0] * K
    for key, ks in members.items():
        vals = rng.sample(range(N), len(ks))
        for k, g in zip(ks, vals):
            gs[k] = g
    same = [[m for m in members[pairs[k]] if m != k] for k in range(K)]

    cur = _cost(a, N, T, ginv, pairs, gs, D)
    for it in range(iters):
        if cur == 0:
            return gs
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        k = rng.randrange(K)
        used = {gs[m] for m in same[k]}
        if len(used) >= N:
            continue
        g = rng.randrange(N)
        while g in used:
            g = rng.randrange(N)
        old = gs[k]
        gs[k] = g
        v = _cost(a, N, T, ginv, pairs, gs, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[k] = old
    return gs if cur == 0 else None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N and random base patterns with a orbits per side."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_TRY]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        ginv = [inv(g) for g in range(N)]
        M = _random_pattern(a, d, rng)
        pairs = [(i, j) for i in range(a) for j in range(a) for _ in range(M[i][j])]
        gs = _anneal(a, N, T, ginv, pairs, D, rng, ITERS, deadline)
        if gs is not None:
            return T, pairs, gs
    return None


def _lift_edges(a, N, T, pairs, gs):
    """Expand a found multi-orbit lift into (n, edges)."""
    aN = a * N
    edges = []
    for (i, j), g in zip(pairs, gs):
        for x in range(N):
            edges.append((i * N + x, aN + j * N + T[x][g]))
    return 2 * aN, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    # Record-matching calibration case: incidence graph of PG(2, d-1).
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
    budget = 2.0
    while time.monotonic() < deadline:
        for a in A_CYCLE:
            if time.monotonic() >= deadline:
                break
            N = max(2, best_n // (2 * a) + 1)
            if 2 * a * N > moore:
                continue
            att_deadline = min(deadline, time.monotonic() + budget)
            res = _attempt(a, N, d, D, rng, att_deadline)
            if res is not None:
                T, pairs, gs = res
                n, e = _lift_edges(a, N, T, pairs, gs)
                consider(n, e)
        budget *= 1.2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
