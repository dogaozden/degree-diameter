import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per order N within one attempt
ITERS = 1500                  # annealing steps per (group, block sizes) try


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
# New idea: two-orbit bi-Cayley lifts.
#
# Base graph: 2 "A" base vertices A_0, A_1 and 2 "B" base vertices B_0, B_1.
# Over a group G of order N we get 4N vertices A_{i,x}, B_{j,y} (x, y in G).
# Block (i, j) carries a connection set S_ij ⊆ G and edges
#     A_{i,x} -- B_{j, x*s}   for every s in S_ij.
# Degree conditions: row sums and column sums of block sizes equal d.
# We use sizes [[a, d-a], [d-a, a]] with 1 <= a <= d-1, which gives
# every A and every B vertex degree exactly d.
#
# Left multiplication by G is an automorphism, so the eccentricities of the
# four base vertices A_0, A_1, B_0, B_1 decide the diameter. This family has
# twice the freedom of a one-orbit bi-Cayley graph, so it can reach orders
# above 2N for the same search effort.
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


def _cost2(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for the four base sources."""
    Sinv = [[[invs[s] for s in S[i][j]] for j in (0, 1)] for i in (0, 1)]
    N2 = 2 * N
    total = 0
    for src in (0, N, N2, N2 + N):
        seen = bytearray(4 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N2:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j in (0, 1):
                        base = N2 + j * N
                        for s in S[i][j]:
                            v = base + row[s]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                else:
                    j, y = divmod(u - N2, N)
                    row = T[y]
                    for i in (0, 1):
                        off = i * N
                        for h in Sinv[i][j]:
                            v = off + row[h]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 4 * N - count
    return total


def _anneal2(N, T, invs, sizes, D, rng, iters, deadline):
    """Simulated annealing over the four block connection sets to zero unreached pairs."""
    S = [[rng.sample(range(N), sizes[i][j]) for j in (0, 1)] for i in (0, 1)]
    cur = _cost2(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(2)
        j = rng.randrange(2)
        blk = S[i][j]
        p = rng.randrange(len(blk))
        c = rng.randrange(N)
        if c in blk:
            continue
        old = blk[p]
        blk[p] = c
        v = _cost2(N, T, invs, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            blk[p] = old
    return S if cur == 0 else None


MAX_GROUPS = MAX_GROUPS_PER_ATTEMPT


def _attempt2(N, d, D, rng, deadline):
    """Try groups of order N until a two-orbit lift with diameter <= D is found, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        a = rng.randint(1, d - 1)
        sizes = [[a, d - a], [d - a, a]]
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal2(N, T, invs, sizes, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _edges2(N, T, S):
    """Materialise the 4N-vertex two-orbit lift as (n, edges)."""
    edges = []
    for i in (0, 1):
        for j in (0, 1):
            for s in S[i][j]:
                for x in range(N):
                    edges.append((i * N + x, 2 * N + j * N + T[x][s]))
    return 4 * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 1.0)
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

    # Two-orbit lifts have 4N vertices, so N <= Moore bound / 4.
    Nmax = lib._moore_bound(d, D) // 4
    N = max(d + 1, best_n // 4 + 1)
    budget = 0.5
    while time.monotonic() < deadline and N <= Nmax:
        now = time.monotonic()
        att_deadline = min(deadline, now + budget)
        res = _attempt2(N, d, D, rng, att_deadline)
        if res is None:
            budget *= 2
            continue
        T, S = res
        n, e = _edges2(N, T, S)
        consider(n, e)
        N += 1
        budget = 0.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
