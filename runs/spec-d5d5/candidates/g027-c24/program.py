import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per (base size, N) attempt
ITERS = 500                   # annealing steps per group
ATTEMPT_BUDGET = 2.5          # seconds per (base size, N) attempt


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
# Group enumeration: semidirect products Z_m x|_r Z_k of order N.
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
# NEW: multi-orbit bi-lift with annealed voltages (non-Cayley bi-regular lift).
#
# Base graph: a "A" vertices and a "B" vertices, each of degree d. Its darts are
# pairings of A-stubs with B-stubs, so a base multigraph is a random d-regular
# bipartite multigraph. Every dart (i, j, g) becomes the edges
#     A_i,x -- B_j, x*g   for all x in G.
# Left multiplication by G is an automorphism, so the diameter test only needs
# BFS from one identity vertex per base orbit. The voltages g are annealed to
# drive the number of unreached (source, vertex) pairs to zero. Duplicate darts
# are penalized so every lifted vertex keeps degree d.
# ----------------------------------------------------------------------------

def _lift_adj(N, a, T, darts):
    """Adjacency of the lift. A_i -> index i*N + x, B_j -> index (a + j)*N + y."""
    V = 2 * a * N
    adj = [[] for _ in range(V)]
    for i, j, g in darts:
        bj = (a + j) * N
        for x in range(N):
            u = i * N + x
            v = bj + T[x][g]
            adj[u].append(v)
            adj[v].append(u)
    return adj


def _cost(N, a, D, T, darts):
    """Unreached (source, vertex) pairs over one identity source per base orbit, plus duplicate penalty."""
    adj = _lift_adj(N, a, T, darts)
    V = len(adj)
    total = 0
    for s in range(2 * a):
        src = s * N
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    total += 20 * (len(darts) - len(set(darts)))
    return total


def _anneal(N, a, d, D, T, rng, iters, deadline):
    """Random d-regular bipartite base pairing, then anneal the voltages."""
    stubsA = [i for i in range(a) for _ in range(d)]
    stubsB = [j for j in range(a) for _ in range(d)]
    rng.shuffle(stubsB)
    darts = [(i, j, rng.randrange(N)) for i, j in zip(stubsA, stubsB)]
    cur = _cost(N, a, D, T, darts)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.2, 3.0 * (1.0 - it / iters))
        k = rng.randrange(len(darts))
        i, j, g = darts[k]
        ng = rng.randrange(N)
        if ng == g:
            continue
        darts[k] = (i, j, ng)
        c = _cost(N, a, D, T, darts)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            darts[k] = (i, j, g)
    return darts if cur == 0 else None


def _attempt(N, a, d, D, rng, deadline):
    """Try groups of order N for a lift with 2a base vertices; return (T, darts) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        darts = _anneal(N, a, d, D, T, rng, ITERS, deadline)
        if darts is not None:
            return T, darts
    return None


def _lift_edges(N, a, T, darts):
    """Deduplicated edge list of the lift."""
    edges = set()
    for i, j, g in darts:
        bj = (a + j) * N
        for x in range(N):
            u = i * N + x
            v = bj + T[x][g]
            edges.add((u, v) if u < v else (v, u))
    return sorted(edges)


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

    # Multi-orbit bi-lift search. Each config is a base size a (2a base vertices).
    # For each a, walk N upward from the smallest value that could beat best_n,
    # round-robin across configs. Retire a config after two failed attempts.
    moore = lib._moore_bound(d, D)
    states = {}
    for a in (2, 3, 1):
        Nmax = moore // (2 * a)
        lo = max(d + 1, best_n // (2 * a) + 1)
        if lo <= Nmax:
            states[a] = [lo, 0, Nmax]

    while time.monotonic() < deadline and states:
        for a in list(states):
            if time.monotonic() >= deadline:
                break
            N, misses, Nmax = states[a]
            if N > Nmax:
                del states[a]
                continue
            att_deadline = min(deadline, time.monotonic() + ATTEMPT_BUDGET)
            res = _attempt(N, a, d, D, rng, att_deadline)
            if res is not None:
                T, darts = res
                consider(2 * a * N, _lift_edges(N, a, T, darts))
                states[a] = [N + 1, 0, Nmax]
            else:
                misses += 1
                if misses >= 2:
                    del states[a]
                else:
                    states[a] = [N + 1, misses, Nmax]

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
