import itertools
import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# New idea: fiber-transitive multi-base voltage lifts.
#
# A bipartite base graph has a parts A_0..A_{a-1} and B_0..B_{a-1}, each base
# vertex of degree d. A dart (i, j, g) joins (A_i, x) to (B_j, x*g) for all x
# in a group G of order N. The lift has 2aN vertices and is bipartite and
# d-regular by construction.
#
# Left multiplication by h in G is an automorphism of every lift, so the
# eccentricity of (A_i, x) equals that of (A_i, e). The diameter check therefore
# needs only 2a BFS runs, from the identity of each base vertex. The base
# pattern is a sum of d random permutations, which is always balanced, and the
# voltages are annealed to remove all pairs at distance > D.
# ----------------------------------------------------------------------------

MAX_GROUPS = 10
ITERS = 1500


# ----------------------------------------------------------------------------
# Baseline families.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Fiber-transitive multi-base lifts over semidirect products Z_m x| Z_k.
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


def _pattern(a, d, rng):
    """Base dart pattern: a sum of d random permutations, so every base vertex has degree d."""
    pairs = []
    for _ in range(d):
        perm = list(range(a))
        rng.shuffle(perm)
        pairs.extend((i, perm[i]) for i in range(a))
    return pairs


def _unreached(a, N, T, darts_A, darts_B, D):
    """Count (base source, vertex) pairs at distance > D, with sources at identity fibers."""
    M = 2 * a
    size = M * N
    total = 0
    for src in range(M):
        seen = bytearray(size)
        s0 = src * N
        seen[s0] = 1
        frontier = [s0]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                s, x = divmod(u, N)
                row = T[x]
                if s < a:
                    for j, g in darts_A[s]:
                        v = (a + j) * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    for i, gi in darts_B[s - a]:
                        v = i * N + row[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += size - count
    return total


def _anneal_lift(a, N, d, D, T, ginv, rng, iters, deadline):
    """Anneal voltages on a random balanced base pattern until every base source reaches all within D."""
    pairs = _pattern(a, d, rng)
    L = len(pairs)
    gs = []
    for p in range(L):
        used = {gs[q] for q in range(p) if pairs[q] == pairs[p]}
        gs.append(rng.choice([g for g in range(N) if g not in used]))

    def evaluate():
        dA = [[] for _ in range(a)]
        dB = [[] for _ in range(a)]
        for (i, j), g in zip(pairs, gs):
            dA[i].append((j, g))
            dB[j].append((i, ginv[g]))
        return _unreached(a, N, T, dA, dB, D)

    cur = evaluate()
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 1.0 + 3.0 * (1.0 - it / iters)
        p = rng.randrange(L)
        used = {gs[q] for q in range(L) if q != p and pairs[q] == pairs[p]}
        g = rng.randrange(N)
        if g in used or g == gs[p]:
            continue
        old = gs[p]
        gs[p] = g
        v = evaluate()
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[p] = old
    if cur == 0:
        return pairs, gs
    return None


def _attempt_lift(a, N, d, D, rng, deadline):
    """Try groups of order N for a base with 2a vertices; return (n, edges) on success, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        ginv = [inv(g) for g in range(N)]
        res = _anneal_lift(a, N, d, D, T, ginv, rng, ITERS, deadline)
        if res is None:
            continue
        pairs, gs = res
        edges = []
        for (i, j), g in zip(pairs, gs):
            for x in range(N):
                edges.append((i * N + x, (a + j) * N + T[x][g]))
        return 2 * a * N, edges
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 5.0)
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

    consider(2, [(0, 1)])

    # Record-matching case for D = 3: incidence graph of PG(2, d-1).
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
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Fiber-transitive multi-base lift search, ascending in vertex count.
    if d >= 2 and D >= 2:
        moore = lib._moore_bound(d, D)
        budget = 0.1
        while time.monotonic() < deadline:
            cands = []
            for a in range(1, 9):
                lo = max(d, best_n // (2 * a) + 1)
                hi = min(moore // (2 * a), lo + 7)
                for N in range(lo, hi + 1):
                    cands.append((2 * a * N, a, N))
            if not cands:
                break
            cands.sort()
            old = best_n
            for size, a, N in cands:
                now = time.monotonic()
                if now >= deadline:
                    break
                res = _attempt_lift(a, N, d, D, rng, min(deadline, now + budget))
                if res is not None:
                    consider(*res)
                    if best_n > old:
                        break
            if best_n == old:
                budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
