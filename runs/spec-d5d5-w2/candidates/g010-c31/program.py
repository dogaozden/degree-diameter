import itertools
import math
import random
import time

import lib

ITERS = 1200            # annealing steps per (group, dart layout) try
T_HOT = 2.0             # initial temperature (unreached-pair units)
T_COLD = 0.2            # final temperature
MAX_GROUPS = 8          # groups tried per attempt
ATTEMPT_CAP = 3.0       # max seconds per attempt
P_SCHEDULE = (2, 3, 2, 3, 1)   # base-graph sizes per side, cycled


# ----------------------------------------------------------------------------
# Baseline families (always validated with lib.is_valid before use).
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
            for p_ in L:
                for r_ in L:
                    if p_ < r_:
                        covered.add((p_, r_))

    edges = []
    for j, L in enumerate(lines):
        for p_ in L:
            edges.append((p_, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-vertex voltage lifts over semidirect products Z_m x|_r Z_k.
#
# Base graph: p vertices on side A and p on side B. Darts (a, b) carry a
# group element ("voltage") g; the lift joins A_(a,x) to B_(b, x*g) for all x.
# Left multiplication by G is an automorphism, transitive on each fiber, so
# the diameter is checked by BFS from one source per base vertex (2p BFS).
# Unlike the single-orbit bi-Cayley search, the base graph (p >= 2) and all
# voltages are searched jointly.
#
# Vertex ids: A_(a,x) = a*N + x ; B_(b,y) = p*N + b*N + y.
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


def _make_tables(m, k, r):
    """Return (N, T, invs): T[x][g] = x*g and invs[g] = g^-1 for the group."""
    N, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    return N, T, invs


def _layout(p, d, rng):
    """Dart layout: d random permutations of range(p), so every base vertex has degree d on each side."""
    darts = []
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        for a in range(p):
            darts.append((a, perm[a]))
    return darts


def _unreached(p, N, T, invs, darts, volts, D):
    """Total (source, vertex) pairs not within distance D, over one source per base vertex."""
    out_d = [[] for _ in range(p)]
    in_d = [[] for _ in range(p)]
    for (a, b), g in zip(darts, volts):
        out_d[a].append((b, g))
        in_d[b].append((a, invs[g]))
    PN = p * N
    V = 2 * PN
    sources = [a * N for a in range(p)] + [PN + b * N for b in range(p)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            if not frontier:
                break
            nxt = []
            for u in frontier:
                if u < PN:
                    a, x = divmod(u, N)
                    row = T[x]
                    for b, g in out_d[a]:
                        v = PN + b * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    b, y = divmod(u - PN, N)
                    row = T[y]
                    for a, hi in in_d[b]:
                        v = a * N + row[hi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(p, N, T, invs, darts, D, rng, iters, deadline):
    """Simulated annealing over the dart voltages to drive unreached pairs to zero."""
    n_d = len(darts)
    volts = [rng.randrange(N) for _ in range(n_d)]
    cur = _unreached(p, N, T, invs, darts, volts, D)
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(n_d)
        old = volts[i]
        new = rng.randrange(N)
        if new == old:
            continue
        volts[i] = new
        v = _unreached(p, N, T, invs, darts, volts, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            volts[i] = old
    if cur == 0:
        return volts
    return None


def _attempt(p, N, d, D, rng, deadline):
    """Try groups of order N and random dart layouts until a valid lift is found or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        Ng, T, invs = _make_tables(m, k, r)
        for _ in range(2):
            if time.monotonic() > deadline:
                return None
            darts = _layout(p, d, rng)
            volts = _anneal(p, Ng, T, invs, darts, D, rng, ITERS, deadline)
            if volts is not None:
                return darts, volts, T, Ng
    return None


def _edges(p, N, T, darts, volts):
    """Build the (vertex count, edge list) of the lift."""
    PN = p * N
    es = set()
    for (a, b), g in zip(darts, volts):
        for x in range(N):
            es.add((a * N + x, PN + b * N + T[x][g]))
    return 2 * PN, sorted(es)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 1.5)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

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

    moore = lib._moore_bound(d, D)
    fails = {p: 0 for p in (1, 2, 3)}
    rr = 0
    idle = 0

    while time.monotonic() < deadline:
        p = P_SCHEDULE[rr % len(P_SCHEDULE)]
        rr += 1
        target_total = best[0] + 1
        N = max(1, -(-target_total // (2 * p)))   # smallest order beating the best so far
        if 2 * p * N > moore:
            idle += 1
            if idle > 2 * len(P_SCHEDULE):
                break
            continue
        idle = 0
        now = time.monotonic()
        budget = min(ATTEMPT_CAP, 1.0 * (1.3 ** fails[p]))
        att_deadline = min(deadline, now + budget)
        res = _attempt(p, N, d, D, rng, att_deadline)
        if res is None:
            fails[p] += 1
            continue
        darts, volts, T, Ng = res
        n, e = _edges(p, Ng, T, darts, volts)
        before = best[0]
        consider(n, e)
        if best[0] > before:
            fails[p] = 0
        else:
            fails[p] += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
