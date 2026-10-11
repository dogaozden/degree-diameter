import itertools
import math
import random
import time

import lib

ITERS = 1500          # annealing steps per (group, base dart configuration)
MAX_GROUPS = 10       # groups tried per (k, N) attempt
T_HOT = 1.5           # initial temperature (unreached-pair units)
T_COLD = 0.1          # final temperature
WINDOW = 16           # pick the next (k, N) among this many smallest sizes above the floor
MAX_BASE = 4          # largest number of base vertices per side
DUP_PENALTY = 3       # cost of a repeated dart (would create a duplicate edge)


# ----------------------------------------------------------------------------
# Baseline families (fast, checked with lib.is_valid before use).
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
# Multi-orbit group lifts.
#
# Base graph: k "A" vertices A_0..A_{k-1} and k "B" vertices B_0..B_{k-1}.
# Each base vertex is a copy of G (|G| = N). A dart (i, j, g) joins
# A_i x to B_j (x g) for every x in G. Left multiplication by G is an
# automorphism of the lift, and the G-orbits are exactly the 2k base vertices.
# So the lift has diameter <= D iff, for each source A_i e and B_j e, every
# vertex is within distance D. That gives 2k sources, not 2.
#
# Base darts form a d-regular bipartite multigraph on k + k vertices. The
# search moves are: relabel a dart's group element, swap the B-endpoints of
# two darts, or swap the A-endpoints of two darts. Each move keeps all base
# degrees equal to d.
#
# The lift has order 2kN. Since k can be 2..4, the lift can reach orders
# that a single bi-Cayley orbit (k = 1) cannot.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, kk, r) with m*kk = N, giving Z_m x|_r Z_kk."""
    out = []
    for kk in range(1, N + 1):
        if N % kk:
            continue
        m = N // kk
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                out.append((m, kk, r))
    return out


def _cost(k, N, T, invT, darts, D):
    """Total unreached (source, vertex) pairs over the 2k orbit representatives, plus duplicate penalties."""
    n = 2 * k * N
    kN = k * N
    adjA = [[] for _ in range(k)]
    adjB = [[] for _ in range(k)]
    keys = set()
    dup = 0
    for i, j, g in darts:
        key = (i, j, g)
        if key in keys:
            dup += 1
        else:
            keys.add(key)
        adjA[i].append((j, g))
        adjB[j].append((i, invT[g]))
    total = DUP_PENALTY * dup
    sources = [i * N for i in range(k)] + [kN + j * N for j in range(k)]
    for src in sources:
        seen = bytearray(n)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < kN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in adjA[i]:
                        v = kN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - kN, N)
                    row = T[y]
                    for i, gi in adjB[j]:
                        v = i * N + row[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += n - count
    return total


def _anneal(k, N, T, invT, d, D, rng, iters, deadline):
    """Anneal base darts to zero unreached pairs. Return the dart list or None."""
    A_slots = [i for i in range(k) for _ in range(d)]
    B_slots = [j for j in range(k) for _ in range(d)]
    rng.shuffle(B_slots)
    darts = [[A_slots[t], B_slots[t], rng.randrange(N)] for t in range(k * d)]
    cur = _cost(k, N, T, invT, darts, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        new = [list(x) for x in darts]
        mv = rng.random()
        if mv < 0.4:
            t = rng.randrange(len(new))
            new[t][2] = rng.randrange(N)
        elif mv < 0.7:
            t1 = rng.randrange(len(new))
            t2 = rng.randrange(len(new))
            if new[t1][1] == new[t2][1]:
                continue
            new[t1][1], new[t2][1] = new[t2][1], new[t1][1]
        else:
            t1 = rng.randrange(len(new))
            t2 = rng.randrange(len(new))
            if new[t1][0] == new[t2][0]:
                continue
            new[t1][0], new[t2][0] = new[t2][0], new[t1][0]
        v = _cost(k, N, T, invT, new, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = new, v
    if cur == 0:
        return darts
    return None


def _attempt(k, N, d, D, rng, deadline):
    """Try groups of order N for base size k; return (n, edges) for the first valid lift, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invT = [inv(g) for g in range(N)]
        darts = _anneal(k, N, T, invT, d, D, rng, ITERS, deadline)
        if darts is not None:
            base = [(i, k + j, g) for i, j, g in darts]
            return lib.group_lift(2 * k, base, N, mul)
    return None


def _candidates(d, D, floor, mb):
    """(size, k, N) triples with floor < 2kN <= mb, sorted ascending by size."""
    out = []
    for k in range(1, MAX_BASE + 1):
        for N in range(2, mb // (2 * k) + 1):
            size = 2 * k * N
            if floor < size <= mb:
                out.append((size, k, N))
    out.sort()
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.82 * time_limit, time_limit - 4.0)
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

    mb = lib._moore_bound(d, D)
    fails = 0
    budget = 0.4
    while time.monotonic() < deadline:
        cands = _candidates(d, D, best_n, mb)
        if not cands:
            break
        _, k, N = rng.choice(cands[:WINDOW])
        att_deadline = min(deadline, time.monotonic() + budget)
        res = _attempt(k, N, d, D, rng, att_deadline)
        if res is None:
            fails += 1
            if fails % 10 == 0:
                budget = min(budget * 1.5, 10.0)
            continue
        n, e = res
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best

