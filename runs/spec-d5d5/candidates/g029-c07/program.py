import itertools
import math
import random
import time

import lib

ITERS = 1000            # annealing steps per (base size, group) attempt
GROUPS_PER_N = 6        # groups tried for each sampled order N
N_WINDOW = 12           # sample group orders in [lo, lo + N_WINDOW]
TRY_BUDGET = 2.5        # seconds per (base size, N, group) attempt


# ----------------------------------------------------------------------------
# Safe baseline families (always validated with lib.is_valid before returning).
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
# Voltage lifts of small bipartite base multigraphs over small groups.
#
# Base: a vertices A_0..A_{a-1} and a vertices B_0..B_{a-1}. Each dart (i, j, g)
# joins A_i,x to B_j,(x*g) for all x in G, where G is a group of order N.
# Every A_i and B_j has exactly d darts, so the lift is d-regular and bipartite.
#
# Left multiplication by h maps A_i,x -> A_i,hx and is an automorphism of the
# lift, so it suffices to run BFS from the identity of each base fiber.
# Vertex index: A_i,x -> i*N + x ;  B_j,y -> (a + j)*N + y.  Identity code is 0.
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


def _group_table(m, k, r):
    """Return (order, T) with T[x][g] = x*g for the group Z_m x|_r Z_k."""
    order, mul, _ = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    return order, T


def _lift_adj(a, N, T, darts):
    """Adjacency lists of the lift of the base graph with the given darts."""
    nv = 2 * a * N
    adj = [[] for _ in range(nv)]
    for i, j, g in darts:
        bj = (a + j) * N
        for x in range(N):
            u = i * N + x
            v = bj + T[x][g]
            adj[u].append(v)
            adj[v].append(u)
    return adj


def _lift_unreached(a, N, T, darts, D):
    """Total count of (source, vertex) pairs at distance > D, over the 2a base fiber identities."""
    nv = 2 * a * N
    adj = _lift_adj(a, N, T, darts)
    total = 0
    for s in range(2 * a):
        src = s * N
        seen = bytearray(nv)
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
        total += nv - cnt
    return total


def _search(a, N, T, d, D, rng, iters, deadline):
    """Anneal the dart labels (group elements) until the lift has diameter <= D."""
    darts = []
    used = {}
    for _ in range(d):
        perm = list(range(a))
        rng.shuffle(perm)
        for i in range(a):
            j = perm[i]
            s = used.setdefault((i, j), set())
            g = rng.randrange(N)
            while g in s:
                g = rng.randrange(N)
            s.add(g)
            darts.append([i, j, g])

    cur = _lift_unreached(a, N, T, darts, D)
    it = 0
    while cur and it < iters and time.monotonic() < deadline:
        it += 1
        t = rng.randrange(len(darts))
        i, j, g = darts[t]
        s = used[(i, j)]
        ng = rng.randrange(N)
        if ng in s:
            continue
        darts[t][2] = ng
        v = _lift_unreached(a, N, T, darts, D)
        temp = max(0.1, 3.0 * (1.0 - it / iters))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            s.discard(g)
            s.add(ng)
            cur = v
        else:
            darts[t][2] = g
    return darts if cur == 0 else None


def _edges_of(a, N, T, darts):
    """Edge list and vertex count of the lift."""
    edges = []
    for i, j, g in darts:
        bj = (a + j) * N
        for x in range(N):
            edges.append((i * N + x, bj + T[x][g]))
    return 2 * a * N, edges


def _lift_search(d, D, best_n, deadline, rng):
    """Search one (base size, order, group) candidate that beats best_n. Return (n, edges) or None."""
    moore = lib._moore_bound(d, D)
    opts = []
    for a in (1, 2, 3, 4):
        lo = max(d + 1, best_n // (2 * a) + 1)
        hi = min(lo + N_WINDOW, moore // (2 * a))
        if lo <= hi:
            opts.append((a, lo, hi))
    if not opts:
        return None

    while time.monotonic() < deadline:
        a, lo, hi = rng.choice(opts)
        N = rng.randint(lo, hi)
        groups = _groups(N)
        rng.shuffle(groups)
        for m, k, r in groups[:GROUPS_PER_N]:
            now = time.monotonic()
            if now >= deadline:
                return None
            order, T = _group_table(m, k, r)
            att_deadline = min(deadline, now + TRY_BUDGET)
            darts = _search(a, order, T, d, D, rng, ITERS, att_deadline)
            if darts is None:
                continue
            n, e = _edges_of(a, order, T, darts)
            if n > best_n and lib.is_valid(n, e, d, D):
                return n, e
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.0, min(0.85 * time_limit, time_limit - 4.0))
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

    # Exact record family: incidence graph of PG(2, d-1).
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

    # Main search: voltage lifts of small bipartite base graphs over small groups.
    if d >= 2 and D >= 2:
        while time.monotonic() < deadline:
            res = _lift_search(d, D, best_n, deadline, rng)
            if res is None:
                break
            consider(*res)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
