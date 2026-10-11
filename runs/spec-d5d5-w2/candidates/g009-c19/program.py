import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 10   # groups tried per order N within one attempt
ITERS = 500                   # annealing steps per (group, block split) try
T_HOT = 1.5                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
BUDGET_START = 3.0            # seconds per target order N, first try
BUDGET_CAP = 20.0             # cap on per-target seconds as failures pile up


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
# NEW: two-orbit bi-Cayley search.
#
# Group G = Z_m x|_r Z_k of order N. Each side has TWO orbits:
#   A_i,x  (i in {0,1}, x in G)   ids: i*N + x
#   B_j,y  (j in {0,1}, y in G)   ids: 2N + j*N + y
# Four blocks (i, j) carry connection sets S_ij with
#   |S_00| = |S_11| = a,  |S_01| = |S_10| = d - a,   1 <= a <= d-1.
# Edge A_i,x -- B_j,x*g for g in S_ij. Every A has degree a + (d-a) = d and
# every B has degree (d-a) + a = d, so the graph is d-regular and bipartite.
#
# Left multiplication by G is an automorphism, so only four BFS sources
# (A_0,0; A_1,0; B_0,0; B_1,0) are needed. The graph has 4N vertices, so
# it beats one-orbit bi-Cayley graphs of the same order by enlarging the search space.
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


def _cost2(N, T, blocks, D):
    """Total unreached (source, vertex) pairs over the four orbit representatives."""
    V = 4 * N
    adj = [[] for _ in range(V)]
    for i, j, S in blocks:
        ob = 2 * N + j * N
        oa = i * N
        for x in range(N):
            row = T[x]
            a_id = oa + x
            lst = adj[a_id]
            for g in S:
                b_id = ob + row[g]
                lst.append(b_id)
                adj[b_id].append(a_id)
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
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


def _anneal2(N, T, a, d, D, rng, iters, deadline):
    """Anneal the four connection sets to zero unreached pairs; return blocks or None."""
    blocks = [
        [0, 0, rng.sample(range(N), a)],
        [0, 1, rng.sample(range(N), d - a)],
        [1, 0, rng.sample(range(N), d - a)],
        [1, 1, rng.sample(range(N), a)],
    ]
    cur = _cost2(N, T, blocks, D)
    for it in range(iters):
        if cur == 0:
            return blocks
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        blk = blocks[rng.randrange(4)]
        k = rng.randrange(len(blk[2]))
        c = rng.randrange(N)
        if c in blk[2]:
            continue
        old = blk[2][k]
        blk[2][k] = c
        v = _cost2(N, T, blocks, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            blk[2][k] = old
    return blocks if cur == 0 else None


def _attempt2(N, d, D, rng, deadline):
    """Try groups of order N until a two-orbit connection pattern has diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        a = rng.randrange(1, d)
        blocks = _anneal2(N, T, a, d, D, rng, ITERS, deadline)
        if blocks is not None:
            return N, T, blocks
    return None


def _edges2(N, T, blocks):
    """Edge list of the two-orbit bi-Cayley graph (4N vertices)."""
    out = []
    for i, j, S in blocks:
        for x in range(N):
            for g in S:
                out.append((i * N + x, 2 * N + j * N + T[x][g]))
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
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

    # Two-orbit bi-Cayley graphs have 4N vertices and must respect the Moore bound.
    Nmax = lib._moore_bound(d, D) // 4
    if Nmax < d + 1:
        return best

    # Ascend from a starting order: each success raises the target by one.
    # Failures at a target grow its budget so the time goes to the hardest step.
    target = max(d + 1, best_n // 4, int(0.47 * Nmax) - 1) + 1
    budget = BUDGET_START
    while time.monotonic() < deadline and target <= Nmax:
        att_deadline = min(deadline, time.monotonic() + budget)
        res = _attempt2(target, d, D, rng, att_deadline)
        if res is not None:
            N, T, blocks = res
            consider(4 * N, _edges2(N, T, blocks))
            target += 1
            budget = BUDGET_START
        else:
            budget = min(BUDGET_CAP, budget * 1.5)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
