import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 4   # groups tried per (a, N) within one attempt
ITERS = 500                  # annealing steps per attempt
T_HOT = 1.5                  # initial annealing temperature (unreached-pair units)
T_COLD = 0.15                # final annealing temperature


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
# Multi-vertex voltage lifts over semidirect groups.
#
# Base: a A-vertices and a B-vertices joined by a d-regular bipartite multigraph
# ("darts"). Dart (i, j, g) joins (A_i, x) to (B_j, x*g) for all x in G.
# Left multiplication by h is an automorphism, so the diameter is the maximum
# eccentricity over the 2a base representatives (A_i, e) and (B_j, e).
# Lift order n = 2*a*N, degree d, bipartite by construction.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _random_darts(a, d, N, rng):
    """d-regular bipartite base on a+a vertices with distinct voltages on parallel darts."""
    Bl = [j for j in range(a) for _ in range(d)]
    rng.shuffle(Bl)
    darts = []
    used = set()
    for idx, j in enumerate(Bl):
        i = idx // d
        g = rng.randrange(N)
        while (i, j, g) in used:
            g = rng.randrange(N)
        used.add((i, j, g))
        darts.append((i, j, g))
    return darts


def _cost(a, N, T, invs, darts, D):
    """Total unreached (source, vertex) pairs over the 2a base representatives."""
    outA = [[] for _ in range(a)]
    inB = [[] for _ in range(a)]
    for i, j, g in darts:
        outA[i].append((j, g))
        inB[j].append((i, invs[g]))
    size = 2 * a * N
    total = 0
    for s in range(2 * a):
        src = s * N                      # block s: s < a is A_s, else B_{s-a}
        seen = bytearray(size)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                blk, x = divmod(v, N)
                row = T[x]
                if blk < a:
                    for j, g in outA[blk]:
                        w = (a + j) * N + row[g]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    for i, gi in inB[blk - a]:
                        w = i * N + row[gi]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += size - count
    return total


def _anneal(a, N, T, invs, darts, D, rng, iters, deadline):
    """Anneal dart voltages to zero the unreached count. Returns darts or None."""
    used = {(i, j, g) for i, j, g in darts}
    cur = _cost(a, N, T, invs, darts, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        k = rng.randrange(len(darts))
        i, j, g = darts[k]
        g2 = rng.randrange(N)
        if g2 == g or (i, j, g2) in used:
            continue
        darts[k] = (i, j, g2)
        v = _cost(a, N, T, invs, darts, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            used.discard((i, j, g))
            used.add((i, j, g2))
            cur = v
        else:
            darts[k] = (i, j, g)
    return darts if cur == 0 else None


def _attempt(a, N, d, D, rng, deadline):
    """Try several groups of order N for base size a; return (T, darts) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        darts = _random_darts(a, d, N, rng)
        res = _anneal(a, N, T, invs, darts, D, rng, ITERS, deadline)
        if res is not None:
            return T, res
    return None


def _lift_edges(a, N, T, darts):
    """Edges of the lift: (A_i, x) -- (B_j, x*g) for each dart (i, j, g)."""
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, (a + j) * N + T[x][g]))
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

    # Safe baselines.
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
    failed = set()
    budget = 2.0

    # Search: smallest candidate orders above the current best first.
    while time.monotonic() < deadline:
        cands = sorted(
            (2 * a * N, a, N)
            for a in (2, 3, 4)
            for N in range(d, moore // (2 * a) + 1)
            if best_n < 2 * a * N <= moore and (a, N) not in failed
        )
        if not cands:
            break

        success = False
        for n_c, a, N in cands[:8]:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(a, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, darts = res
            consider(2 * a * N, _lift_edges(a, N, T, darts))
            if best_n >= n_c:
                success = True
                break
            failed.add((a, N))
        if not success:
            budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
