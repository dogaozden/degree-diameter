import itertools
import math
import random
import time

import lib

GROUPS_PER_N = 12      # groups tried per (p, N) attempt
ITERS = 1500           # annealing steps per attempt
SLACK = 6              # orders tried above the current floor
MAX_BUDGET = 6.0       # cap on per-attempt time (seconds)
P_CHOICES = (1, 2, 2, 3, 3, 4)


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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit voltage lifts over semidirect groups Z_m x| Z_k.
#
# Base: p "A" vertices and p "B" vertices, joined by a d-regular bipartite
# multigraph given by a p x p count matrix (row and column sums = d). Each
# base dart (i, j) carries a group voltage g; its lift joins A(i, x) to
# B(j, x*g) for every x in G. Its multiplicity counts distinct voltages.
# Left multiplication by G is an automorphism, so eccentricities from the
# 2p sources A(i, e), B(j, e) decide the diameter.
#
# The parent uses p = 1 only. Here p > 1 gives 2pN vertices with N near
# target/(2p), so the group orders are much smaller and the search is cheaper.
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


def _base_counts(p, d, rng):
    """Random d-regular p x p count matrix: sum of d random permutation matrices."""
    counts = [[0] * p for _ in range(p)]
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        for i in range(p):
            counts[i][perm[i]] += 1
    return counts


def _adjacency(p, N, T, invs, darts):
    """Adjacency lists of the lift. A(i,x) = i*N+x, B(j,y) = p*N + j*N + y."""
    nv = 2 * p * N
    outs = [[] for _ in range(p)]
    ins = [[] for _ in range(p)]
    for i, j, g in darts:
        outs[i].append((p * N + j * N, g))
        ins[j].append((i * N, invs[g]))
    adj = [None] * nv
    for i in range(p):
        for x in range(N):
            Tx = T[x]
            adj[i * N + x] = [base + Tx[g] for base, g in outs[i]]
    for j in range(p):
        for y in range(N):
            Ty = T[y]
            adj[p * N + j * N + y] = [base + Ty[h] for base, h in ins[j]]
    return adj


def _unreached(adj, nv, sources, D):
    """Count (source, vertex) pairs at distance more than D over the given sources."""
    total = 0
    for s in sources:
        seen = bytearray(nv)
        seen[s] = 1
        frontier = [s]
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
        total += nv - cnt
    return total


def _anneal(p, N, T, invs, darts, D, rng, iters, deadline):
    """Anneal voltages on fixed base darts so that all source eccentricities are <= D."""
    nv = 2 * p * N
    sources = [i * N for i in range(p)] + [p * N + j * N for j in range(p)]
    cur = _unreached(_adjacency(p, N, T, invs, darts), nv, sources, D)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        k = rng.randrange(len(darts))
        i, j, _ = darts[k]
        g = rng.randrange(N)
        # Voltages on one base pair must stay distinct (else duplicate edges).
        if any(dg == g for di, dj, dg in darts if di == i and dj == j):
            continue
        cand = darts[:]
        cand[k] = (i, j, g)
        v = _unreached(_adjacency(p, N, T, invs, cand), nv, sources, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = cand, v
    return darts if cur == 0 else None


def _attempt(p, d, N, D, rng, deadline):
    """Try groups of order N with a random d-regular base on p + p vertices."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_N]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        counts = _base_counts(p, d, rng)
        darts = []
        for i in range(p):
            for j in range(p):
                if counts[i][j]:
                    for g in rng.sample(range(N), counts[i][j]):
                        darts.append((i, j, g))
        res = _anneal(p, N, T, invs, darts, D, rng, ITERS, deadline)
        if res is not None:
            return T, res
    return None


def _edges(p, N, T, darts):
    """Edge list of the lift (distinct by construction)."""
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, p * N + j * N + T[x][g]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 4.0)
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

    moore = lib._moore_bound(d, D)
    budget = 0.5
    fails = 0

    # Ladder search: always aim one step above the current best order.
    while time.monotonic() < deadline:
        options = []
        for p in P_CHOICES:
            lo = max(d, -(-(best_n + 2) // (2 * p)))
            hi = min(moore // (2 * p), lo + SLACK)
            if lo <= hi:
                options.append((p, lo, hi))
        if not options:
            break
        p, lo, hi = rng.choice(options)
        N = rng.randint(lo, hi)

        now = time.monotonic()
        att_deadline = min(deadline, now + budget)
        res = _attempt(p, d, N, D, rng, att_deadline)
        if res is not None:
            T, darts = res
            consider(2 * p * N, _edges(p, N, T, darts))
            fails = 0
            budget = 0.5
        else:
            fails += 1
            if fails % 6 == 0:
                budget = min(budget * 1.5, MAX_BUDGET)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
