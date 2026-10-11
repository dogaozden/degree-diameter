import itertools
import math
import random
import time

import lib

ITERS = 350                  # annealing steps per (group, dart configuration) try
MAX_GROUPS_PER_ATTEMPT = 6   # groups tried per (k, N) attempt
KS = (2, 3, 4)               # base-graph sides: k A-vertices and k B-vertices


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
# New construction: multi-orbit voltage lifts over finite groups.
#
# Base graph: k A-blocks and k B-blocks, with d darts out of each A-block and
# d darts into each B-block (a d-regular bipartite multigraph on k + k nodes).
# A dart (i, j, g) joins A_{i,x} to B_{j, x*g} for every x in G. Left
# multiplication by G is an automorphism, so only 2k BFS sources (one per
# block) are needed to certify diameter <= D. Groups are semidirect products
# Z_m x| Z_k2 of order N. Total order 2kN, and the search is simulated
# annealing over the dart labels, which is different from the single-orbit
# bi-Cayley search.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k2, r) with m*k2 = N, giving Z_m x|_r Z_k2."""
    out = []
    for k2 in range(1, N + 1):
        if N % k2:
            continue
        m = N // k2
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    return out


def _adj(k, N, MT, darts):
    """Adjacency lists of the lift. A-block i is vertices i*N..i*N+N-1; B-block j is (k+j)*N..."""
    V = 2 * k * N
    adj = [[] for _ in range(V)]
    for i, j, g in darts:
        ai = i * N
        bj = (k + j) * N
        for x in range(N):
            a = ai + x
            b = bj + MT[x][g]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _cost(k, N, MT, darts, D):
    """Count (source, vertex) pairs at distance > D, over one source per block."""
    adj = _adj(k, N, MT, darts)
    V = 2 * k * N
    sources = [i * N for i in range(k)] + [(k + j) * N for j in range(k)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += V - cnt
    return total


def _init_darts(k, d, N, rng):
    """Random d-regular base dart set with distinct (i, j, g) triples."""
    A = [i for i in range(k) for _ in range(d)]
    B = [j for j in range(k) for _ in range(d)]
    rng.shuffle(B)
    darts = []
    used = set()
    for i, j in zip(A, B):
        g = rng.randrange(N)
        for _ in range(1000):
            if (i, j, g) not in used:
                break
            g = rng.randrange(N)
        used.add((i, j, g))
        darts.append((i, j, g))
    return darts


def _anneal(k, N, MT, darts, D, rng, iters, deadline):
    """Anneal dart labels and B-assignments to zero unreached pairs; return darts or None."""
    cur = _cost(k, N, MT, darts, D)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = max(0.2, 2.0 * (1.0 - it / iters))
        new = darts[:]
        if rng.random() < 0.6:
            t = rng.randrange(len(new))
            i, j, _ = new[t]
            new[t] = (i, j, rng.randrange(N))
        else:
            t1, t2 = rng.sample(range(len(new)), 2)
            i1, j1, g1 = new[t1]
            i2, j2, g2 = new[t2]
            if j1 == j2:
                continue
            new[t1] = (i1, j2, g1)
            new[t2] = (i2, j1, g2)
        if len(set(new)) != len(new):
            continue
        c = _cost(k, N, MT, new, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            darts, cur = new, c
    return darts if cur == 0 else None


def _attempt(k, N, d, D, rng, deadline):
    """Try groups of order N for base size k; return (darts, MT) on success, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k2, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k2, r)
        MT = [[mul(x, g) for g in range(N)] for x in range(N)]
        darts = _init_darts(k, d, N, rng)
        res = _anneal(k, N, MT, darts, D, rng, ITERS, deadline)
        if res is not None:
            return res, MT
    return None


def _edges(k, N, MT, darts):
    """Return (n, edges) for the lift."""
    adj = _adj(k, N, MT, darts)
    edges = []
    for a in range(k * N):
        for b in adj[a]:
            edges.append((a, b))
    return 2 * k * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
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

    # Araujo-Pardo & Lopez family for D = 3 when d - 2 is a prime power.
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

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
    budget = 0.6
    while time.monotonic() < deadline:
        cands = []
        for k in KS:
            lo = best_n // (2 * k) + 1
            for N in range(max(lo, 2), lo + 3):
                n = 2 * k * N
                if best_n < n <= moore:
                    cands.append((n, k, N))
        if not cands:
            break
        cands.sort()

        progress = False
        for n, k, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(k, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            darts, MT = res
            n2, e2 = _edges(k, N, MT, darts)
            consider(n2, e2)
            progress = True
            break
        if not progress:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
