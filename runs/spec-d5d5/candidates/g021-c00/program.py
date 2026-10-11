import itertools
import math
import random
import time

import lib

# New construction family (not in the parent): two-orbit bi-Cayley graphs.
# Vertices A_{i,x} and B_{j,y} for i, j in {0,1} and x, y in a group G of order N.
# A_{i,x} is joined to B_{j, x*s} for each s in S[i][j]. The split matrix
# [[a, d-a], [d-a, a]] makes every vertex degree d, with 1 <= a <= d-1 so the
# graph is connected. Left multiplication is an automorphism, so the diameter
# is decided by BFS from the four sources A_{0,e}, A_{1,e}, B_{0,e}, B_{1,e}.
# Order 4N, which can beat single-orbit bi-Cayley graphs of order 2N.

ITERS = 500
TIME_FRAC = 0.82
ATTEMPT_BUDGET = 3.5
FINAL_BUDGET = 4.0


# ----------------------------------------------------------------------------
# Baseline families.
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Two-orbit bi-Cayley search.
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


def _unreached(N, T, R, S, D):
    """Count unreached (source, vertex) pairs for the four orbit sources.

    Node ids: A_{i,x} = i*N + x (0..2N-1), B_{j,y} = 2N + j*N + y.
    A_{i,x} ~ B_{j, T[x][s]} for s in S[i][j].
    B_{j,y} ~ A_{i, R[y][s]} for s in S[i][j], where R[y][s] = y * s^{-1}.
    """
    total = 0
    twoN = 2 * N
    M = 4 * N
    for src in (0, N, twoN, twoN + N):
        seen = bytearray(M)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < twoN:
                    i = 0 if u < N else 1
                    x = u - i * N
                    Tx = T[x]
                    for j in (0, 1):
                        base = twoN + j * N
                        for s in S[i][j]:
                            v = base + Tx[s]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                else:
                    w = u - twoN
                    j = 0 if w < N else 1
                    y = w - j * N
                    Ry = R[y]
                    for i in (0, 1):
                        base = i * N
                        for s in S[i][j]:
                            v = base + Ry[s]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += M - count
    return total


def _anneal(N, T, R, sizes, D, rng, iters, deadline):
    """Anneal the four connection sets (fixed sizes) to zero unreached pairs."""
    S = [[rng.sample(range(N), sizes[i][j]) for j in range(2)] for i in range(2)]
    cur = _unreached(N, T, R, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = max(0.3, 3.0 * (1.0 - it / iters))
        i = rng.randrange(2)
        j = rng.randrange(2)
        cell = S[i][j]
        k = rng.randrange(len(cell))
        c = rng.randrange(N)
        if c in cell:
            continue
        old = cell[k]
        cell[k] = c
        v = _unreached(N, T, R, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            cell[k] = old
    return S if cur == 0 else None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N, cycling through the split choices, until one works."""
    groups = _groups(N)
    rng.shuffle(groups)
    splits = [a for a in range(1, d) if a <= N and d - a <= N]
    if not splits:
        return None
    for idx, (m, k, r) in enumerate(groups):
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        invs = [inv(g) for g in range(N)]
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        R = [[mul(y, invs[g]) for g in range(N)] for y in range(N)]
        a = splits[idx % len(splits)]
        sizes = [[a, d - a], [d - a, a]]
        S = _anneal(N, T, R, sizes, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _graph(N, T, S):
    """Edge list of the two-orbit bi-Cayley graph (4N vertices)."""
    edges = []
    for i in range(2):
        for j in range(2):
            base_a = i * N
            base_b = 2 * N + j * N
            for x in range(N):
                Tx = T[x]
                for s in S[i][j]:
                    edges.append((base_a + x, base_b + Tx[s]))
    return 4 * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + TIME_FRAC * time_limit
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

    # Four orbits of size N: 4N <= Moore bound.
    Nmax = lib._moore_bound(d, D) // 4
    if Nmax < d:
        return best

    def try_n(N, budget):
        att_deadline = min(deadline, time.monotonic() + budget)
        return _attempt(N, d, D, rng, att_deadline)

    def record(N, res):
        T, S = res
        n, e = _graph(N, T, S)
        consider(n, e)

    # Binary search for the largest feasible N in [lo, Nmax].
    lo = max(d, best_n // 4)
    hi = Nmax
    if lo > hi:
        lo = hi
    while lo < hi and time.monotonic() < deadline:
        mid = (lo + hi + 1) // 2
        res = try_n(mid, ATTEMPT_BUDGET)
        if res is not None:
            record(mid, res)
            lo = mid
        else:
            hi = mid - 1

    # Use leftover time to push one order at a time above the best success.
    while time.monotonic() < deadline and lo + 1 <= Nmax:
        res = try_n(lo + 1, FINAL_BUDGET)
        if res is not None:
            record(lo + 1, res)
            lo += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
