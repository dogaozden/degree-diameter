import itertools
import math
import random
import time

import lib

NMAX = 400              # cap on group order (keeps multiplication tables small)
ITERS = 500             # annealing steps per restart
RESTARTS = 3            # random base graphs per group
ATTEMPT_GROUPS = 6      # groups tried per (a, N) attempt
T_HOT = 4.0             # initial annealing temperature (unreached-vertex units)
T_COLD = 0.2            # final annealing temperature
BUDGET_START = 0.6      # seconds per (a, N) config in the first round
BUDGET_GROW = 1.3
BUDGET_CAP = 8.0
WIN_BASE = 24           # total-order window above the current best, first round
WIN_GROW = 16           # window growth per round


# ----------------------------------------------------------------------------
# Baseline families (cheap, always checked with lib.is_valid).
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
# Bold new construction: non-bi-Cayley group voltage lifts over a random
# REGULAR base multigraph with a A-vertices and a B-vertices (a = 1..4).
#
# Base: A_i and B_j, with dart count M[i][j] (row and column sums = d).
# Each dart (i, j, g) over a finite group G of order N gives the edges
#     (A_i, x) -- (B_j, x*g)   for all x in G.
# Left multiplication by G is an automorphism, and it acts transitively on
# each fibre, so the diameter is decided by one source per base vertex.
# Total order = 2 * a * N. Search over voltages by simulated annealing,
# minimising the number of unreached (source, vertex) pairs.
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


def _random_base(a, d, rng):
    """Random a x a count matrix with all row and column sums equal to d (sum of d permutations)."""
    M = [[0] * a for _ in range(a)]
    for _ in range(d):
        p = list(range(a))
        rng.shuffle(p)
        for i in range(a):
            M[i][p[i]] += 1
    return M


def _random_darts(M, N, rng):
    """Darts [i, j, g] with distinct voltages for each (i, j) pair (no duplicate edges)."""
    darts = []
    for i, row in enumerate(M):
        for j, c in enumerate(row):
            if c:
                for g in rng.sample(range(N), c):
                    darts.append([i, j, g])
    return darts


def _cost(darts, a, N, D, T, ginv):
    """Total unreached (source, vertex) pairs over one source per base vertex."""
    V = 2 * a * N
    off = a * N
    Aout = [[] for _ in range(a)]
    Bin = [[] for _ in range(a)]
    for i, j, g in darts:
        Aout[i].append((j, g))
        Bin[j].append((i, ginv[g]))
    total = 0
    for s in range(2 * a):
        src = s * N if s < a else off + (s - a) * N
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < off:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in Aout[i]:
                        v = off + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - off, N)
                    row = T[y]
                    for i, h in Bin[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(a, N, d, D, T, ginv, rng, deadline):
    """Anneal voltages on a random regular base until every source reaches all within D."""
    darts = _random_darts(_random_base(a, d, rng), N, rng)
    cur = _cost(darts, a, N, D, T, ginv)
    for it in range(ITERS):
        if cur == 0:
            return darts
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        idx = rng.randrange(len(darts))
        i, j, old = darts[idx]
        used = {g for ii, jj, g in darts if ii == i and jj == j}
        g = rng.randrange(N)
        if g in used:
            continue
        darts[idx][2] = g
        v = _cost(darts, a, N, D, T, ginv)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[idx][2] = old
    if cur == 0:
        return darts
    return None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N with random base graphs until a valid lift is found or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:ATTEMPT_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        ginv = [inv(g) for g in range(N)]
        for _ in range(RESTARTS):
            if time.monotonic() > deadline:
                return None
            darts = _anneal(a, N, d, D, T, ginv, rng, deadline)
            if darts is not None:
                return darts, T
    return None


def _edges(darts, a, N, T):
    """Expand a voltage assignment into (n, edges)."""
    off = a * N
    E = []
    for i, j, g in darts:
        for x in range(N):
            E.append((i * N + x, off + j * N + T[x][g]))
    return 2 * a * N, E


def _configs(lo, hi, d):
    """(total, a, N) with lo < 2*a*N <= hi, sorted by total ascending."""
    out = []
    for a in (1, 2, 3, 4):
        step = 2 * a
        Nlo = max(d + 1, lo // step + 1)
        Nhi = min(hi // step, NMAX)
        for N in range(Nlo, Nhi + 1):
            out.append((step * N, a, N))
    out.sort()
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.8 * time_limit, time_limit - 6.0))
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

    # Safe baselines.
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

    # Bold search: voltage lifts over random regular base multigraphs.
    if d >= 3 and D >= 2:
        moore = lib._moore_bound(d, D)
        best_total = best[0]
        rnd = 0
        while time.monotonic() < deadline and best_total < moore:
            hi = min(moore, best_total + WIN_BASE + WIN_GROW * rnd)
            cfgs = _configs(best_total, hi, d)
            if not cfgs:
                if hi >= moore:
                    break
                rnd += 1
                continue
            budget = min(BUDGET_CAP, BUDGET_START * BUDGET_GROW ** rnd)
            for total, a, N in cfgs:
                if total <= best_total:
                    continue
                now = time.monotonic()
                if now >= deadline:
                    break
                att = min(deadline, now + budget)
                res = _attempt(a, N, d, D, rng, att)
                if res is None:
                    continue
                darts, T = res
                n, E = _edges(darts, a, N, T)
                if n > best[0] and lib.is_valid(n, E, d, D):
                    best = (n, E)
                    best_total = n
            rnd += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
