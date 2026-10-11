import itertools
import math
import random
import time

import lib

GROUP_TRIES = 8        # groups tried per (base size, order N) attempt
ITERS = 6000           # annealing steps per (group, base-voltage) try
BASES = (2, 3)         # base multigraph sizes b (b vertices on each side)


# ----------------------------------------------------------------------------
# Baseline families (fast, always checked with lib.is_valid).
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
# New family: voltage lifts of small bipartite base multigraphs over
# semidirect products Z_m x| Z_k.
#
# Base: b vertices A_0..A_{b-1} and b vertices B_0..B_{b-1}. The base has d
# "darts" per A-vertex: for each t in 0..d-1 and i in 0..b-1 there is a dart
# from A_i to B_{P[t][i]}, where P[t] is a permutation of range(b). Each dart
# carries a voltage V[t][i] in the group G of order N.
#
# Lift: vertices (f, x) with fiber f in 0..2b-1 and x in G. The dart (A_i -> B_j, g)
# joins (A_i, x) to (B_j, x*g) for all x. Left multiplication by G is an
# automorphism, so the diameter is at most D iff every fiber representative
# (f, identity) reaches all 2bN vertices within D steps.
#
# Parallel darts with the same (i, j) need distinct voltages to keep the graph simple.
# Result: 2bN vertices, degree d, bipartite, b*d*N edges.
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


def _cost(b, N, d, D, T, invs, P, V):
    """Number of (source fiber representative, vertex) pairs not within distance D."""
    adjA = [[] for _ in range(b)]
    adjB = [[] for _ in range(b)]
    for t in range(d):
        Pt = P[t]
        Vt = V[t]
        for i in range(b):
            j = Pt[i]
            g = Vt[i]
            adjA[i].append(((b + j) * N, g))
            adjB[j].append((i * N, invs[g]))
    M = 2 * b * N
    total = 0
    for src in range(2 * b):
        seen = bytearray(M)
        s = src * N
        seen[s] = 1
        frontier = [s]
        reached = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                fib, x = divmod(u, N)
                row = T[x]
                if fib < b:
                    for off, g in adjA[fib]:
                        v = off + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    for off, h in adjB[fib - b]:
                        v = off + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            reached += len(nxt)
            frontier = nxt
        total += M - reached
    return total


def _ok(P, V, d, t, i, g):
    """True if voltage g on dart (t, i) does not duplicate an edge set with another parallel dart."""
    j = P[t][i]
    for t2 in range(d):
        if t2 != t and P[t2][i] == j and V[t2][i] == g:
            return False
    return True


def _anneal(b, N, d, D, T, invs, rng, iters, deadline):
    """Anneal voltages (and random base permutations) to zero unreached pairs."""
    P = [rng.sample(range(b), b) for _ in range(d)]
    V = [[None] * b for _ in range(d)]
    for t in range(d):
        for i in range(b):
            for _ in range(200):
                g = rng.randrange(N)
                if _ok(P, V, d, t, i, g):
                    V[t][i] = g
                    break
            else:
                return None
    cur = _cost(b, N, d, D, T, invs, P, V)
    for it in range(iters):
        if cur == 0:
            return P, V
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        t = rng.randrange(d)
        i = rng.randrange(b)
        g = rng.randrange(N)
        if g == V[t][i] or not _ok(P, V, d, t, i, g):
            continue
        old = V[t][i]
        V[t][i] = g
        v = _cost(b, N, d, D, T, invs, P, V)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            V[t][i] = old
    if cur == 0:
        return P, V
    return None


def _attempt(b, N, d, D, rng, deadline):
    """Try groups of order N for base size b until a valid lift is found or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    tries = groups[:GROUP_TRIES]
    for idx, (m, k, r) in enumerate(tries):
        now = time.monotonic()
        if now >= deadline:
            return None
        left = len(tries) - idx
        sub = min(deadline, now + (deadline - now) / left)
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        res = _anneal(b, N, d, D, T, invs, rng, ITERS, sub)
        if res is not None:
            P, V = res
            return b, N, T, P, V
    return None


def _lift_edges(b, N, d, T, P, V):
    """Edge list and vertex count of the lift described by (b, N, T, P, V)."""
    edges = []
    for t in range(d):
        for i in range(b):
            j = P[t][i]
            g = V[t][i]
            for x in range(N):
                edges.append((i * N + x, (b + j) * N + T[x][g]))
    return 2 * b * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 1.0
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
            return True
        return False

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    # Safe fallbacks.
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
    bad = set()
    budget = 2.0

    # Main search: voltage lifts of small base multigraphs. Each step aims for
    # the smallest order that beats the current best for each base size b.
    while time.monotonic() < deadline:
        cands = []
        for b in BASES:
            N = best_n // (2 * b) + 1
            if 2 * b * N <= moore and (b, N) not in bad:
                cands.append((b, N))
        if not cands:
            break

        progress = False
        for b, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(b, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            bb, NN, T, P, V = res
            n, edges = _lift_edges(bb, NN, d, T, P, V)
            if consider(n, edges):
                progress = True
                break
            bad.add((b, N))
        if not progress:
            budget = min(budget * 1.5, 25.0)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
