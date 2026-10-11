import itertools
import math
import random
import time

import lib

ITERS = 700                   # annealing steps per (group, orbit matrix) try
T_HOT = 1.2                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.1                  # final annealing temperature
MAX_GROUPS = 10               # groups tried per (t, N) attempt
ORBIT_COUNTS = (1, 2, 3, 4)   # t = number of A-orbits (and of B-orbits)
POOL = 60                     # top candidates (by order) eligible in a pass
PER_PASS = 10                 # candidates attempted per pass
BUDGET_START = 0.6            # seconds per attempt in the first pass
BUDGET_CAP = 4.0              # cap on per-attempt seconds
FLOOR_START = 0.6             # search vertex totals >= FLOOR_START * Moore first
FLOOR_MIN = 0.45              # lowest fraction of the Moore bound ever searched
FLOOR_STEP = 0.02


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
# Group G = Z_m x| Z_k of order N acts regularly on each of t "A-orbits"
# A^0..A^{t-1} and t "B-orbits" B^0..B^{t-1}. For each pair (i, j) there is a
# connection set S_ij of size c_ij, giving edges A^i_x -- B^j_{x s} for s in S_ij.
# The matrix c is circulant with row and column sums d, so the graph is d-regular
# with 2tN vertices. Left multiplication by G is an automorphism, so the diameter
# is decided by BFS from one representative per orbit (2t sources).
# t = 1 recovers the single bi-Cayley family; t >= 2 gives larger orders at the
# same degree.
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


def _orbit_matrix(t, d, rng):
    """Circulant t x t matrix of non-negative integers with every row and column summing to d."""
    q = [d // t + (1 if k < d % t else 0) for k in range(t)]
    rng.shuffle(q)
    c = [[0] * t for _ in range(t)]
    for i in range(t):
        for k in range(t):
            c[i][(i + k) % t] = q[k]
    return c


def _reach(src, t, N, adjA, adjB, D):
    """Number of vertices within distance D of src in the multi-orbit lift."""
    base = t * N
    seen = bytearray(2 * base)
    seen[src] = 1
    frontier = [src]
    count = 1
    T = None  # set per call through closure below
    return count, frontier, seen


def _cost(t, N, T, adjA, adjB, D):
    """Total unreached (source, vertex) pairs over one representative per orbit."""
    base = t * N
    V = 2 * base
    total = 0
    sources = list(range(0, base, N)) + list(range(base, V, N))
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < base:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, s in adjA[i]:
                        v = base + j * N + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - base, N)
                    row = T[y]
                    for i, sinv in adjB[j]:
                        v = i * N + row[sinv]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _adjacency(t, invs, cells, state):
    """Per-orbit neighbour lists: adjA[i] holds (j, s); adjB[j] holds (i, s^-1)."""
    adjA = [[] for _ in range(t)]
    adjB = [[] for _ in range(t)]
    for (i, j, _), S in zip(cells, state):
        for s in S:
            adjA[i].append((j, s))
            adjB[j].append((i, invs[s]))
    return adjA, adjB


def _anneal(t, N, T, invs, cells, D, rng, deadline):
    """Anneal connection sets so that all orbit representatives reach everything within D."""
    state = [rng.sample(range(N), c) for (_, _, c) in cells]
    adjA, adjB = _adjacency(t, invs, cells, state)
    cur = _cost(t, N, T, adjA, adjB, D)
    for it in range(ITERS):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        k = rng.randrange(len(cells))
        S = state[k]
        pos = rng.randrange(len(S))
        g = rng.randrange(N)
        if g in S:
            continue
        new_S = S[:]
        new_S[pos] = g
        trial = state[:]
        trial[k] = new_S
        tA, tB = _adjacency(t, invs, cells, trial)
        v = _cost(t, N, T, tA, tB, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            state, cur = trial, v
    if cur == 0:
        return state
    return None


def _attempt(t, N, d, D, rng, deadline):
    """Try groups of order N for a t-orbit lift; return (n, edges) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    base = t * N
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        cmat = _orbit_matrix(t, d, rng)
        cells = [(i, j, cmat[i][j]) for i in range(t) for j in range(t) if cmat[i][j] > 0]
        state = _anneal(t, N, T, invs, cells, D, rng, deadline)
        if state is not None:
            edges = []
            for (i, j, _), S in zip(cells, state):
                for s in S:
                    for x in range(N):
                        edges.append((i * N + x, base + j * N + T[x][s]))
            return 2 * base, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
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
    floor_frac = FLOOR_START
    budget = BUDGET_START

    # Pass-based search over (t, N) with total order 2tN above the best so far.
    while time.monotonic() < deadline:
        best_total = best_n
        cands = []
        for t in ORBIT_COUNTS:
            if t > d:
                continue
            Nhi = moore // (2 * t)
            if Nhi < d:
                continue
            target = max(best_total + 1, int(floor_frac * moore))
            Nlo = max(d, -(-target // (2 * t)))
            for N in range(Nlo, Nhi + 1):
                cands.append((2 * t * N, t, N))
        if not cands:
            if floor_frac > FLOOR_MIN:
                floor_frac = max(FLOOR_MIN, floor_frac - FLOOR_STEP)
                continue
            break
        cands.sort(reverse=True)
        pool = cands[:POOL]
        picks = rng.sample(pool, min(PER_PASS, len(pool)))

        success = False
        for _, t, N in picks:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(t, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            consider(*res)
            success = True
            break

        if not success:
            if budget < BUDGET_CAP:
                budget = min(BUDGET_CAP, budget * 1.5)
            elif floor_frac > FLOOR_MIN:
                floor_frac = max(FLOOR_MIN, floor_frac - FLOOR_STEP)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
