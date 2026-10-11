import itertools
import math
import random
import time

import lib

MAX_GROUPS = 6     # groups tried per attempt
ITERS = 4000       # annealing steps per (group, base matrix) try
WINDOW = 12        # even orders above the incumbent tried per pass


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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-block bi-Cayley lifts over semidirect products Z_m x| Z_k.
#
# Vertex blocks A_0..A_{b-1} and B_0..B_{b-1}, each block a copy of G (|G| = N).
# A dart (i, j, g) joins A_i^x to B_j^{x g} for every x in G.
# The base multigraph M[i][j] (darts from A_i to B_j) is d-regular on both sides,
# so every vertex has degree exactly d and the graph is bipartite.
# Left multiplication by G is an automorphism, so the 2b BFS sources
# A_i^e and B_j^e decide the diameter exactly.
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


def _mul_table(m, k, r):
    """Full multiplication table T[x][g] = x * g for Z_m x|_r Z_k."""
    order, mul, _ = lib.semidirect_group(m, k, r)
    return [[mul(x, g) for g in range(order)] for x in range(order)]


def _random_base(b, d, rng):
    """Random d-regular b x b nonnegative integer matrix (sum of d random permutations)."""
    M = [[0] * b for _ in range(b)]
    for _ in range(d):
        p = list(range(b))
        rng.shuffle(p)
        for i in range(b):
            M[i][p[i]] += 1
    return M


def _cost(b, N, T, darts, D):
    """Number of (source, vertex) pairs not within distance D, over the 2b block sources."""
    n = 2 * b * N
    adj = [[] for _ in range(n)]
    for i, j, g in darts:
        ba = i * N
        bb = (b + j) * N
        for x in range(N):
            a = ba + x
            y = bb + T[x][g]
            adj[a].append(y)
            adj[y].append(a)
    total = 0
    sources = [i * N for i in range(b)] + [(b + j) * N for j in range(b)]
    for s in sources:
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
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
        total += n - count
    return total


def _anneal(b, N, T, pairs, rng, D, deadline):
    """Anneal the group labels of the darts to zero unreached pairs."""
    K = len(pairs)
    gs = []
    for k in range(K):
        used = {gs[t] for t in range(k) if pairs[t] == pairs[k]}
        g = rng.randrange(N)
        while g in used:
            g = rng.randrange(N)
        gs.append(g)
    darts = [(pairs[k][0], pairs[k][1], gs[k]) for k in range(K)]
    cur = _cost(b, N, T, darts, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        k = rng.randrange(K)
        p = pairs[k]
        used = {gs[t] for t in range(K) if t != k and pairs[t] == p}
        g = rng.randrange(N)
        if g in used or g == gs[k]:
            continue
        old = gs[k]
        gs[k] = g
        darts[k] = (p[0], p[1], g)
        v = _cost(b, N, T, darts, D)
        temp = max(0.05, 2.0 * (1.0 - it / ITERS))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[k] = old
            darts[k] = (p[0], p[1], old)
    return darts if cur == 0 else None


def _attempt(b, N, d, D, rng, end):
    """Try groups of order N (random base matrices) until one gives diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() >= end:
            break
        T = _mul_table(m, k, r)
        M = _random_base(b, d, rng)
        pairs = [(i, j) for i in range(b) for j in range(b) for _ in range(M[i][j])]
        darts = _anneal(b, N, T, pairs, rng, D, end)
        if darts is not None:
            return b, N, darts, T
    return None


def _edges(b, N, T, darts):
    """Edge list and order of the lift."""
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, (b + j) * N + T[x][g]))
    return 2 * b * N, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0] = n
            best[1] = e

    def done():
        return (best[0], best[1])

    if d == 1:
        consider(2, [(0, 1)])
        return done()
    if d == 2:
        if D >= 2:
            n = 2 * D
            consider(n, [(k, (k + 1) % n) for k in range(n)])
        else:
            consider(2, [(0, 1)])
        return done()
    if D == 1:
        consider(2, [(0, 1)])
        return done()

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return done()

    # Safe fallbacks.
    consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Multi-block lift search: climb even orders above the incumbent.
    moore = lib._moore_bound(d, D)
    budget = 0.5
    while time.monotonic() < deadline:
        T0 = best[0] + 1
        if T0 % 2:
            T0 += 1
        if T0 > moore:
            break
        Tend = min(T0 + 2 * (WINDOW - 1), moore)
        found = False
        before = best[0]
        for T in range(T0, Tend + 1, 2):
            if time.monotonic() >= deadline:
                break
            for b in (1, 2, 3):
                if T % (2 * b):
                    continue
                N = T // (2 * b)
                if N < d:
                    continue
                if time.monotonic() >= deadline:
                    break
                end = min(deadline, time.monotonic() + budget)
                res = _attempt(b, N, d, D, rng, end)
                if res is not None:
                    n, e = _edges(*res)
                    consider(n, e)
                    if best[0] > before:
                        found = True
                        break
            if found:
                break
        if not found:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return done()
