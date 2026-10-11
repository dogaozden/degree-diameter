import itertools
import math
import random
import time

import lib

MAX_GROUP_SLICE = 0.5   # minimum seconds given to one group inside an attempt
MARGIN = 0.8            # fraction of time_limit we are willing to use


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
# NEW: two-orbit bi-Cayley lifts over semidirect products.
#
# The parent uses one A-orbit and one B-orbit (a single base edge set). Here we
# use a orbits on each side (a in {1, 2}), so the graph has 2*a*N vertices:
#   A_{i,x} ~ B_{j, x*s} for every dart (i, j, s), s in S_{ij}.
# Left multiplication by G acts on every orbit, so distances from the
# representatives A_{i,e} and B_{j,e} decide the diameter.
# The split of the degree d into counts c_ij (rows and columns each summing
# to d) is random, so asymmetric two-orbit bases are explored, which the
# parent never tries. Within a (i, j) block the connection elements are
# distinct, so the graph is simple.
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


def _count_matrix(a, d, rng):
    """Degree split c[i][j] with every row and column summing to d (no disconnecting splits)."""
    if a == 1:
        return [[d]]
    k = rng.randint(1, d - 1)
    return [[k, d - k], [d - k, k]]


def _unreached(N, a, T, invs, S, D):
    """Count (source, vertex) pairs at distance > D, over sources A_{i,e} and B_{j,e}."""
    outA = [[] for _ in range(a)]
    inB = [[] for _ in range(a)]
    for (i, j), lst in S.items():
        for s in lst:
            outA[i].append((j, s))
            inB[j].append((i, invs[s]))
    aN = a * N
    V = 2 * aN
    total = 0
    sources = [i * N for i in range(a)] + [aN + j * N for j in range(a)]
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        cnt = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < aN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, s in outA[i]:
                        v = aN + j * N + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - aN, N)
                    row = T[y]
                    for i, h in inB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - cnt
    return total


def _anneal(N, a, d, T, invs, c, D, rng, deadline):
    """Simulated annealing over the connection sets to zero unreached pairs."""
    keys = [(i, j) for i in range(a) for j in range(a) if c[i][j] > 0]
    S = {(i, j): rng.sample(range(N), c[i][j]) for (i, j) in keys}
    cur = _unreached(N, a, T, invs, S, D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - (now - start) / span))
        key = keys[rng.randrange(len(keys))]
        lst = S[key]
        p = rng.randrange(len(lst))
        x = rng.randrange(N)
        if x in lst:
            continue
        old = lst[p]
        lst[p] = x
        v = _unreached(N, a, T, invs, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            lst[p] = old
    return S if cur == 0 else None


def _attempt(N, a, d, D, rng, deadline):
    """Try groups of order N (time shared among them) until one yields diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    c = _count_matrix(a, d, rng)
    for idx, (m, k, r) in enumerate(groups):
        now = time.monotonic()
        if now >= deadline:
            break
        remaining = len(groups) - idx
        slice_end = min(deadline, now + max(MAX_GROUP_SLICE, (deadline - now) / remaining))
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal(N, a, d, T, invs, c, D, rng, slice_end)
        if S is not None:
            return T, S
    return None


def _edges(N, a, T, S):
    """Edge list of the two-orbit bi-Cayley graph described by T and S."""
    aN = a * N
    edges = []
    for (i, j), lst in S.items():
        for s in lst:
            for x in range(N):
                edges.append((i * N + x, aN + j * N + T[x][s]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + MARGIN * time_limit
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
    # Per number of A-orbits a, the smallest N that could beat best_n.
    def frontier(a):
        return max(d + 1, best_n // (2 * a) + 1)

    def nmax(a):
        return moore // (2 * a)

    budget = 0.5
    while time.monotonic() < deadline:
        progress = False
        for a in (2, 1):
            tried = 0
            N = frontier(a)
            while tried < 2 and N <= nmax(a):
                now = time.monotonic()
                if now >= deadline:
                    break
                att_deadline = min(deadline, now + budget)
                res = _attempt(N, a, d, D, rng, att_deadline)
                tried += 1
                if res is not None:
                    T, S = res
                    consider(2 * a * N, _edges(N, a, T, S))
                    progress = True
                    break
                N += 1
        if not progress:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
