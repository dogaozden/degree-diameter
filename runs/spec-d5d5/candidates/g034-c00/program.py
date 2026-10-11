import itertools
import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# Search parameters.
#
# Main idea (new in this version): multi-orbit voltage lifts. The base graph has
# p A-vertices and p B-vertices. Its darts come from d random permutations of
# range(p), so every base vertex has degree d and the base graph is d-regular
# (bipartite, possibly with parallel darts). Each dart carries a voltage in a
# finite group G of order N (Z_m x| Z_k). The lift has 2pN vertices and degree d.
#
# Left multiplication by G is an automorphism of the lift, so the diameter test
# only needs BFS from the 2p base vertices (x = identity). The cost is the total
# number of unreached (source, target) pairs, which annealing drives to zero.
# ----------------------------------------------------------------------------

MAX_GROUPS = 10          # groups tried per (p, N) before giving up
ATTEMPTS_PER_GROUP = 3   # random base graphs tried per group
ITERS = 500              # annealing steps per attempt
SLICE = 8.0              # seconds allowed for one (p, N) order before moving on
ORBIT_COUNTS = (2, 3, 4) # numbers of A-orbits (and B-orbits) to try


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
# Group helpers.
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


# ----------------------------------------------------------------------------
# Multi-orbit voltage-lift search.
# ----------------------------------------------------------------------------

def _random_darts(p, d, rng):
    """Base darts (i, j) from d random permutations of range(p); each vertex gets degree d."""
    darts = []
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        darts.extend((i, perm[i]) for i in range(p))
    return darts


def _cost(p, N, T, invs, darts, volt, D):
    """Number of (source, target) pairs at distance > D, sources = the 2p base vertices with x = identity."""
    nb = 2 * p
    adj = [[] for _ in range(nb)]
    for (i, j), g in zip(darts, volt):
        adj[i].append((p + j, g))
        adj[p + j].append((i, invs[g]))
    tot = nb * N
    total = 0
    for src in range(nb):
        seen = bytearray(tot)
        s0 = src * N
        seen[s0] = 1
        frontier = [s0]
        count = 1
        for _ in range(D):
            nxt = []
            for w in frontier:
                u, x = divmod(w, N)
                row = T[x]
                for v, h in adj[u]:
                    y = v * N + row[h]
                    if not seen[y]:
                        seen[y] = 1
                        nxt.append(y)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += tot - count
    return total


def _anneal(p, N, T, invs, darts, D, rng, iters, end):
    """Anneal the voltages on fixed darts until every base source reaches everything within D."""
    nd = len(darts)
    volt = [rng.randrange(N) for _ in range(nd)]
    cur = _cost(p, N, T, invs, darts, volt, D)
    for it in range(iters):
        if cur == 0:
            return volt
        if time.monotonic() > end:
            break
        k = rng.randrange(nd)
        g = rng.randrange(N)
        if g == volt[k]:
            continue
        old = volt[k]
        volt[k] = g
        v = _cost(p, N, T, invs, darts, volt, D)
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            volt[k] = old
    return volt if cur == 0 else None


def _try_order(p, N, d, D, rng, end):
    """Try groups of order N with p orbits until one base graph and voltage set succeeds."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > end:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        for _ in range(ATTEMPTS_PER_GROUP):
            if time.monotonic() > end:
                return None
            darts = _random_darts(p, d, rng)
            volt = _anneal(p, N, T, invs, darts, D, rng, ITERS, end)
            if volt is not None:
                return darts, volt, T
    return None


def _lift_edges(p, N, darts, volt, T):
    """Edges of the lift: dart (i, j) with voltage g joins (A_i, x) to (B_j, x*g)."""
    E = set()
    for (i, j), g in zip(darts, volt):
        for x in range(N):
            a = i * N + x
            b = (p + j) * N + T[x][g]
            E.add((min(a, b), max(a, b)))
    return 2 * p * N, sorted(E)


def _search(d, D, rng, deadline, best_n):
    """Improve on best_n by searching multi-orbit lifts; return (n, edges) for the best valid find, or None."""
    moore = lib._moore_bound(d, D)
    found = None
    orbit_list = ORBIT_COUNTS
    for idx, p in enumerate(orbit_list):
        now = time.monotonic()
        if now >= deadline:
            break
        phase_end = now + (deadline - now) / (len(orbit_list) - idx)
        N = best_n // (2 * p) + 1          # smallest N with 2pN > best_n
        Nmax = moore // (2 * p)
        while N <= Nmax and time.monotonic() < phase_end:
            slice_end = min(phase_end, time.monotonic() + SLICE)
            res = _try_order(p, N, d, D, rng, slice_end)
            if res is None:
                break
            darts, volt, T = res
            n, e = _lift_edges(p, N, darts, volt, T)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n = n
                found = (n, e)
            N = best_n // (2 * p) + 1
    return found


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.78 * time_limit
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

    if D == 1:
        consider(2, [(0, 1)])
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

    if d >= 2 and D >= 2 and time.monotonic() < deadline:
        found = _search(d, D, rng, deadline, best[0])
        if found is not None:
            consider(*found)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
