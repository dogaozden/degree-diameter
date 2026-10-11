import itertools
import math
import random
import time

import lib

ATTEMPT_SECONDS = 2.0   # wall-clock budget for one (group, sizes, sets) annealing attempt
ITER_CAP = 4000         # hard cap on annealing steps per attempt
TIME_FRACTION = 0.80    # fraction of time_limit we are willing to use


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
# Multi-orbit bi-Cayley lifts (new family).
#
# Take a group G of order N (semidirect product Z_m x| Z_k) and t "A-orbits"
# and t "B-orbits". Vertices are A_{i,x} and B_{j,y} for i, j < t and x, y in G.
# For each pair (i, j) choose a connection set S[i][j] of size sz[i][j], and join
#     A_{i,x} -- B_{j, x*s}   for s in S[i][j].
# Left multiplication by G is an automorphism that acts regularly on each orbit,
# so the diameter is decided by BFS from the t + t representatives A_{i,e}, B_{j,e}.
# Row and column sums of sz equal d, so every vertex has degree exactly d.
# The size pattern sz is a sum of d random permutation matrices, which keeps
# sums equal to d for any t.
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


def _perm_sizes(t, d, rng):
    """Random t x t nonnegative integer matrix whose rows and columns each sum to d."""
    sz = [[0] * t for _ in range(t)]
    for _ in range(d):
        p = list(range(t))
        rng.shuffle(p)
        for i in range(t):
            sz[i][p[i]] += 1
    return sz


def _random_sets(sz, N, rng):
    """Random connection sets with the prescribed sizes (distinct elements inside each set)."""
    t = len(sz)
    return [[rng.sample(range(N), sz[i][j]) for j in range(t)] for i in range(t)]


def _cost(N, t, D, M, inv, S):
    """Total number of (source, vertex) pairs not within distance D, over the 2t representatives."""
    tN = t * N
    size = 2 * tN
    Adarts = [[] for _ in range(t)]
    Bdarts = [[] for _ in range(t)]
    for i in range(t):
        for j in range(t):
            for s in S[i][j]:
                Adarts[i].append((j, s))
                Bdarts[j].append((i, inv[s]))
    sources = [i * N for i in range(t)] + [tN + j * N for j in range(t)]
    total = 0
    for src in sources:
        seen = bytearray(size)
        seen[src] = 1
        cnt = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < tN:
                    i, x = divmod(u, N)
                    row = M[x]
                    for j, s in Adarts[i]:
                        v = tN + j * N + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - tN, N)
                    row = M[y]
                    for i, s in Bdarts[j]:
                        v = i * N + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += size - cnt
    return total


def _anneal(N, t, D, M, inv, sz, rng, deadline):
    """Simulated annealing over connection sets until the total unreached count is zero."""
    S = _random_sets(sz, N, rng)
    cur = _cost(N, t, D, M, inv, S)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    it = 0
    while cur > 0 and it < ITER_CAP:
        now = time.monotonic()
        if now > deadline:
            break
        it += 1
        frac = (now - start) / span
        temp = max(0.05, 2.0 * (1.0 - frac))
        i = rng.randrange(t)
        j = rng.randrange(t)
        if not S[i][j]:
            continue
        p = rng.randrange(len(S[i][j]))
        c = rng.randrange(N)
        if c in S[i][j]:
            continue
        old = S[i][j][p]
        S[i][j][p] = c
        v = _cost(N, t, D, M, inv, S)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            S[i][j][p] = old
    return S if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + TIME_FRACTION * time_limit
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

    # Multi-orbit lifts with t A-orbits and t B-orbits: order 2*t*N.
    orbit_counts = [t for t in (2, 3) if moore // (2 * t) >= d + 1]
    if not orbit_counts:
        return best

    while time.monotonic() < deadline:
        t = rng.choice(orbit_counts)
        # Need 2*t*N > best_n to improve, and 2*t*N <= Moore bound.
        Nlo = max(d + 1, best_n // (2 * t) + 1)
        Nhi = moore // (2 * t)
        if Nlo > Nhi:
            orbit_counts = [u for u in orbit_counts if u != t]
            if not orbit_counts:
                break
            continue
        N = Nlo if rng.random() < 0.5 else Nlo + rng.randrange(0, 4)
        N = min(N, Nhi)

        groups = _groups(N)
        if not groups:
            continue
        m, k, r = rng.choice(groups)
        _, mul, inv_f = lib.semidirect_group(m, k, r)
        M = [[mul(x, g) for g in range(N)] for x in range(N)]
        inv = [inv_f(g) for g in range(N)]

        sz = _perm_sizes(t, d, rng)
        att_deadline = min(deadline, time.monotonic() + ATTEMPT_SECONDS)
        S = _anneal(N, t, D, M, inv, sz, rng, att_deadline)
        if S is None:
            continue

        tN = t * N
        edges = []
        for i in range(t):
            for j in range(t):
                for s in S[i][j]:
                    for x in range(N):
                        edges.append((i * N + x, tN + j * N + M[x][s]))
        consider(2 * tN, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
