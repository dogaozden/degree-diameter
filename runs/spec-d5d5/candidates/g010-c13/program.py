import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 8    # groups tried per (p, N) attempt
ITERS = 4000                  # annealing steps per (group, multiplicity matrix) try
T_HOT = 3.0                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.2                  # final annealing temperature
PS = (2, 3, 4)                # base-graph sizes per side for voltage lifts


# ----------------------------------------------------------------------------
# Safe baseline families (always validated with lib.is_valid before use).
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
# New construction: voltage lifts of bipartite base multigraphs with p vertices
# per side over finite groups Z_m x| Z_k of order N.
#
# Base: p A-vertices and p B-vertices, biadjacency multiplicity matrix M with
# row and column sums d (a sum of d random permutation matrices). Each base dart
# (i, j) carries a distinct group voltage g. The lift has vertices A(i,x), B(j,y)
# with x, y in G, and edges A(i,x) -- B(j, x*g). Left multiplication by G is an
# automorphism, so distances from the 2p sources A(i,e), B(j,e) decide the
# diameter. Degree is exactly d and the graph is bipartite by construction.
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


def _random_multiplicity(p, d, rng):
    """p x p nonnegative integer matrix with all row and column sums d (sum of d permutations)."""
    M = [[0] * p for _ in range(p)]
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        for i in range(p):
            M[i][perm[i]] += 1
    return M


def _unreached(p, N, D, adjA, adjB, T):
    """Count (source, vertex) pairs at distance > D, summed over the 2p base sources at identity."""
    pN = p * N
    V = 2 * pN
    total = 0
    for s in range(2 * p):
        src = s * N
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < pN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in adjA[i]:
                        v = (p + j) * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - pN, N)
                    row = T[y]
                    for i, h in adjB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(p, N, D, blocks, T, invs, rng, deadline, iters):
    """Anneal distinct voltages per base block to make every source reach all vertices within D.

    Returns the voltage lists (one list per block) on success, else None.
    """
    volts = [rng.sample(range(N), c) for (_, _, c) in blocks]

    def cost(vs):
        adjA = [[] for _ in range(p)]
        adjB = [[] for _ in range(p)]
        for (i, j, _), vv in zip(blocks, vs):
            for g in vv:
                adjA[i].append((j, g))
                adjB[j].append((i, invs[g]))
        return _unreached(p, N, D, adjA, adjB, T)

    cur = cost(volts)
    for it in range(iters):
        if cur == 0:
            return volts
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        bi = rng.randrange(len(blocks))
        vv = volts[bi]
        t = rng.randrange(len(vv))
        g = rng.randrange(N)
        if g in vv:
            continue
        old = vv[t]
        vv[t] = g
        v = cost(volts)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            vv[t] = old
    return volts if cur == 0 else None


def _attempt(p, N, d, D, rng, deadline):
    """Try groups of order N and random base multiplicity matrices until a lift has diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        M = _random_multiplicity(p, d, rng)
        blocks = [(i, j, M[i][j]) for i in range(p) for j in range(p) if M[i][j] > 0]
        volts = _anneal(p, N, D, blocks, T, invs, rng, deadline, ITERS)
        if volts is not None:
            edges = []
            for (i, j, _), vv in zip(blocks, volts):
                for g in vv:
                    for x in range(N):
                        edges.append((i * N + x, (p + j) * N + T[x][g]))
            return 2 * p * N, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.8 * time_limit, time_limit - 3.0))
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
    if D == 3 and d >= 2 and lib.is_prime_power(d - 1):
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

    if d < 3 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    Ps = [p for p in PS if moore // (2 * p) >= d + 1]
    budget = {p: 1.0 for p in Ps}

    # Round-robin over base sizes p. Each attempt targets a lift order just above the
    # current best, so every success raises the record bar for the next attempt.
    while time.monotonic() < deadline and Ps:
        for p in Ps:
            if time.monotonic() >= deadline:
                break
            lo = max(d + 1, best_n // (2 * p) + 1)
            hi_p = moore // (2 * p)
            if lo > hi_p:
                continue
            hi = min(hi_p, lo + 3)
            N = rng.randint(lo, hi)
            now = time.monotonic()
            att_deadline = min(deadline, now + budget[p])
            res = _attempt(p, N, d, D, rng, att_deadline)
            if res is not None:
                n, e = res
                consider(n, e)
                budget[p] = 1.0
            else:
                budget[p] = min(budget[p] * 1.3, 8.0)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
