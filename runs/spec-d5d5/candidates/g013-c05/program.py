import itertools
import math
import random
import time

import lib

ITERS = 1500            # annealing steps per attempt
ATTEMPT_BUDGET = 3.0    # seconds per (base size, group) attempt
GROUPS_PER_N = 4        # groups tried per sampled order N
SPREAD = 4              # sample N in [lo, lo + SPREAD]
DUP_PENALTY = 200       # cost per duplicate lift edge
BASE_CHOICES = (1, 2, 2, 3, 3, 4)


# ----------------------------------------------------------------------------
# Baseline families (fast, always validated with lib.is_valid).
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
# Voltage lifts over base graphs with `a` vertices per side.
#
# Base: d perfect matchings (permutations) between A_0..A_{a-1} and B_0..B_{a-1},
# giving a d-regular bipartite multigraph with a*d darts. Each dart t carries a
# voltage g in a finite group G of order N. Lift vertices: A_{i,x} and B_{j,y}.
# Dart (i -> j, g) joins A_{i,x} to B_{j, x*g} for all x.
#
# Left multiplication by G is an automorphism, so eccentricities need only be
# checked from one source per base class (2a sources in total).
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


def _lift_cost(vol, perms, a, d, D, N, M, invs):
    """Number of (source, vertex) pairs not within D, plus a penalty for duplicate lift edges."""
    aN = a * N
    V = 2 * aN
    outd = [[] for _ in range(a)]
    ind = [[] for _ in range(a)]
    keys = set()
    dup = 0
    for t, g in enumerate(vol):
        k, i = divmod(t, a)
        j = perms[k][i]
        key = (i, j, g)
        if key in keys:
            dup += 1
        keys.add(key)
        outd[i].append((j, g))
        ind[j].append((i, invs[g]))

    total = 0
    sources = [i * N for i in range(a)] + [aN + j * N for j in range(a)]
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < aN:
                    i, x = divmod(u, N)
                    row = M[x]
                    for j, g in outd[i]:
                        v = aN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - aN, N)
                    row = M[y]
                    for i, gi in ind[j]:
                        v = i * N + row[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            if not nxt:
                break
            frontier = nxt
        total += V - cnt
    return total + DUP_PENALTY * dup


def _anneal(a, N, d, D, perms, M, invs, rng, deadline):
    """Anneal the voltages to zero unreached pairs. Returns the voltage list or None."""
    vol = [rng.randrange(N) for _ in range(a * d)]
    cur = _lift_cost(vol, perms, a, d, D, N, M, invs)
    for it in range(ITERS):
        if cur == 0:
            return vol
        if time.monotonic() > deadline:
            break
        t = rng.randrange(a * d)
        g = rng.randrange(N)
        if g == vol[t]:
            continue
        old = vol[t]
        vol[t] = g
        c = _lift_cost(vol, perms, a, d, D, N, M, invs)
        temp = max(0.05, 2.0 * (1.0 - it / ITERS))
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            vol[t] = old
    return vol if cur == 0 else None


def _lift_edges(a, N, d, perms, vol, M):
    """Build the (vertex count, edge list) of the lift."""
    aN = a * N
    E = []
    for t, g in enumerate(vol):
        k, i = divmod(t, a)
        j = perms[k][i]
        for x in range(N):
            E.append((i * N + x, aN + j * N + M[x][g]))
    return 2 * aN, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 3.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 1:
        consider(2, [(0, 1)])
        return best

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

    if D < 2:
        return best

    moore = lib._moore_bound(d, D)

    # Search: lifts over base graphs with a vertices per side, targeting order > best.
    while time.monotonic() < deadline:
        feasible = [a for a in (1, 2, 3, 4)
                    if best[0] // (2 * a) + 1 <= moore // (2 * a)]
        if not feasible:
            break
        a = rng.choice([b for b in BASE_CHOICES if b in feasible])
        lo = best[0] // (2 * a) + 1
        hi = moore // (2 * a)
        N = rng.randint(lo, min(hi, lo + SPREAD))

        groups = _groups(N)
        rng.shuffle(groups)
        for m, k, r in groups[:GROUPS_PER_N]:
            if time.monotonic() > deadline:
                break
            order, mul, inv = lib.semidirect_group(m, k, r)
            M = [[mul(x, g) for g in range(N)] for x in range(N)]
            invs = [inv(g) for g in range(N)]
            perms = [rng.sample(range(a), a) for _ in range(d)]
            att_deadline = min(deadline, time.monotonic() + ATTEMPT_BUDGET)
            vol = _anneal(a, N, d, D, perms, M, invs, rng, att_deadline)
            if vol is not None:
                n, edges = _lift_edges(a, N, d, perms, vol, M)
                consider(n, edges)
                break

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
