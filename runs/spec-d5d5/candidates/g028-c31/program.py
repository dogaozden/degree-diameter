import itertools
import math
import random
import time

import lib

ITERS = 1500          # annealing steps per random base matrix
T_HOT = 2.0           # starting temperature (in unreached-pair units)
T_COLD = 0.2          # final temperature
MAX_GROUPS = 3        # groups tried per attempt
ATTEMPT_FAILS = 8     # consecutive failures before the per-attempt budget doubles
TMAX = 4              # maximum number of vertex orbits per side
INF = float("inf")


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
# Groups: semidirect products Z_m x|_r Z_k of order N.
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


def _tables(m, k, r):
    """Multiplication table T[x][g] = x*g and inverse list for the group, elements 0..N-1 (0 = identity)."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    return T, invs


# ----------------------------------------------------------------------------
# New construction: multi-orbit bi-Cayley voltage lifts.
#
# Base graph: t "A" orbits and t "B" orbits, with a random base multigraph M
# (t x t, row and column sums d, built as a sum of d random permutation
# matrices). Each base dart (i, j, g) gives the edges A_{i,x} -- B_{j, x*g}
# for all x in G. Every vertex then has degree exactly d, the graph is
# bipartite, and left multiplication by G is an automorphism that is
# transitive on each orbit. So the diameter check needs BFS from only the
# 2t orbit representatives. The t = 1 case is the classic bi-Cayley search.
#
# Annealing moves replace one voltage inside a cell, keeping voltages
# distinct within a cell so no edge is doubled. Acceptance uses a pre-drawn
# Metropolis threshold, so a cost evaluation can stop as soon as the running
# total passes that threshold.
# ----------------------------------------------------------------------------

def _random_base(t, d, rng):
    """t x t nonnegative integer matrix with all row and column sums equal to d."""
    M = [[0] * t for _ in range(t)]
    for _ in range(d):
        perm = list(range(t))
        rng.shuffle(perm)
        for i in range(t):
            M[i][perm[i]] += 1
    return M


def _cost(darts, t, N, T, invs, D, limit):
    """Total unreached (source, vertex) pairs from the 2t orbit representatives.

    Returns early with a value > limit as soon as the running total exceeds limit.
    """
    tN = t * N
    V = 2 * tN
    outA = [[] for _ in range(t)]
    inB = [[] for _ in range(t)]
    for i, j, g in darts:
        outA[i].append((j, g))
        inB[j].append((i, invs[g]))
    total = 0
    sources = [i * N for i in range(t)] + [tN + j * N for j in range(t)]
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < tN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in outA[i]:
                        v = tN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - tN, N)
                    row = T[y]
                    for i, h in inB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
        if total > limit:
            return total
    return total


def _anneal(t, d, D, N, T, invs, rng, deadline):
    """Anneal voltages on a random base matrix until every orbit reaches all vertices within D."""
    M = _random_base(t, d, rng)
    darts = []
    for i in range(t):
        for j in range(t):
            for g in rng.sample(range(N), M[i][j]):
                darts.append([i, j, g])
    cur = _cost(darts, t, N, T, invs, D, INF)
    for it in range(ITERS):
        if cur == 0:
            return darts
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        k = rng.randrange(len(darts))
        i, j, old = darts[k]
        c = rng.randrange(N)
        if c == old or any(a == i and b == j and g == c for a, b, g in darts):
            continue
        darts[k][2] = c
        r = max(rng.random(), 1e-12)
        limit = cur - temp * math.log(r)   # accept iff v <= limit (Metropolis)
        v = _cost(darts, t, N, T, invs, D, limit)
        if v <= limit:
            cur = v
        else:
            darts[k][2] = old
    return darts if cur == 0 else None


def _attempt(t, N, d, D, rng, deadline):
    """Try groups of order N with t orbits until a valid voltage assignment appears or time runs out."""
    groups = _groups(N)
    if not groups:
        return None
    rng.shuffle(groups)
    groups = groups[:MAX_GROUPS]
    for idx, (m, k, r) in enumerate(groups):
        now = time.monotonic()
        if now >= deadline:
            return None
        share = (deadline - now) / (len(groups) - idx)
        gdead = now + share
        T, invs = _tables(m, k, r)
        while time.monotonic() < gdead:
            res = _anneal(t, d, D, N, T, invs, rng, gdead)
            if res is not None:
                return T, res
    return None


def _edges(t, N, T, darts):
    """Expand base darts into the explicit bipartite edge list on 2tN vertices."""
    tN = t * N
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, tN + j * N + T[x][g]))
    return 2 * tN, edges


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
            return True
        return False

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

    Moore = lib._moore_bound(d, D)

    def candidates():
        out = []
        for t in range(1, TMAX + 1):
            for N in range(d + 1, Moore // (2 * t) + 1):
                n = 2 * t * N
                if best_n < n <= Moore:
                    out.append((n, rng.random(), t, N))
        out.sort()
        return out

    cands = candidates()
    pos = 0
    budget = 1.0
    fails = 0

    while time.monotonic() < deadline:
        cands = [c for c in cands if c[0] > best_n]
        if not cands:
            break
        if pos >= len(cands):
            pos = 0
            budget *= 2
        _, _, t, N = cands[pos]
        now = time.monotonic()
        if now >= deadline:
            break
        att_deadline = min(deadline, now + budget)
        res = _attempt(t, N, d, D, rng, att_deadline)
        if res is None:
            pos += 1
            fails += 1
            if fails >= ATTEMPT_FAILS:
                budget *= 2
                fails = 0
            continue
        T, darts = res
        nn, e = _edges(t, N, T, darts)
        if consider(nn, e):
            # Only larger orders can improve now; the filter above drops the rest.
            pos = 0
        else:
            cands.pop(pos)
        fails = 0

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
