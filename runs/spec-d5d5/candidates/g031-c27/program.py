import itertools
import math
import random
import time

import lib

ITERS = 1000                  # annealing steps per (group, base matrix, voltage) try
T_HOT = 2.0                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.1                  # final annealing temperature
ATTEMPT_BUDGET = 1.2          # seconds per (order, base size) attempt
GROUPS_PER_ATTEMPT = 6        # groups tried per attempt
BASE_SIZES = (2, 3, 1)        # base bipartite sizes p (p x p darts-matrix, each side p vertices)


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
# Voltage lifts of small bipartite base multigraphs over groups.
#
# Base: p vertices A_0..A_{p-1} and p vertices B_0..B_{p-1}. Base multigraph
# has M[i][j] darts between A_i and B_j, where M is a sum of d permutation
# matrices, so every base vertex has degree d. Each dart carries a distinct
# voltage s (distinct within one (i, j) pair, which avoids duplicate edges).
# Lift over a group G of order N: vertices (A_i, x) and (B_j, y) with
# (A_i, x) -- (B_j, x*s) for each dart (i, j, s). Left multiplication is an
# automorphism, so eccentricities are constant on each fiber and only the
# 2p fiber identities need BFS checks.
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


def _random_matrix(p, d, rng):
    """Sum of d random permutation matrices of size p: nonnegative integers, row and column sums d."""
    M = [[0] * p for _ in range(p)]
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        for i in range(p):
            M[i][perm[i]] += 1
    return M


def _cost(p, N, T, flat, D):
    """Total number of (fiber identity, vertex) pairs not within distance D."""
    V = 2 * p * N
    boff = p * N
    adj = [[] for _ in range(V)]
    for i, j, s in flat:
        ao = i * N
        bo = boff + j * N
        for x in range(N):
            a = ao + x
            b = bo + T[x][s]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    sources = [i * N for i in range(p)] + [boff + j * N for j in range(p)]
    for src in sources:
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


def _anneal(p, N, T, M, D, rng, iters, deadline):
    """Anneal the voltages of the darts (distinct per (i, j)) to zero unreached pairs.

    Returns the flat dart list [[i, j, s], ...] on success, else None.
    """
    flat = []
    for i in range(p):
        for j in range(p):
            if M[i][j] > N:
                return None
            for s in rng.sample(range(N), M[i][j]):
                flat.append([i, j, s])
    cur = _cost(p, N, T, flat, D)
    for it in range(iters):
        if cur == 0:
            return flat
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        t = rng.randrange(len(flat))
        i, j, old = flat[t]
        c = rng.randrange(N)
        if any(u[0] == i and u[1] == j and u[2] == c for u in flat):
            continue
        flat[t][2] = c
        v = _cost(p, N, T, flat, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            flat[t][2] = old
    if cur == 0:
        return flat
    return None


def _attempt(N, p, d, D, rng, deadline):
    """Try groups of order N with random base matrices until voltages give diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        M = _random_matrix(p, d, rng)
        flat = _anneal(p, N, T, M, D, rng, ITERS, deadline)
        if flat is not None:
            return T, flat
    return None


def _lift_edges(p, N, T, flat):
    """Edges of the lift; vertices A_i,x -> i*N+x and B_j,y -> p*N+j*N+y."""
    boff = p * N
    out = []
    for i, j, s in flat:
        for x in range(N):
            out.append((i * N + x, boff + j * N + T[x][s]))
    return 2 * p * N, out


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

    Vmax = lib._moore_bound(d, D)
    pairs = []
    for p in BASE_SIZES:
        for N in range(1, Vmax // (2 * p) + 1):
            V = 2 * p * N
            if best_n < V <= Vmax:
                pairs.append((V, p, N))
    pairs.sort()

    for V, p, N in pairs:
        if time.monotonic() >= deadline:
            break
        if V <= best_n:
            continue
        att_deadline = min(deadline, time.monotonic() + ATTEMPT_BUDGET)
        res = _attempt(N, p, d, D, rng, att_deadline)
        if res is None:
            continue
        T, flat = res
        n, e = _lift_edges(p, N, T, flat)
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
