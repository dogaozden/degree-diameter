import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per order N within one attempt
ITERS = 600                   # annealing steps per (group, connection set) try
T_HOT = 1.5                   # initial annealing temperature (in unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
WINDOW_FRAC = 0.95            # search only N in [WINDOW_FRAC * top, top] first
BUDGET_START = 0.4            # seconds per (N) attempt in the first pass
BUDGET_CAP = 3.0              # cap on per-attempt seconds as passes fail

# Two-orbit-per-side (2x2 base) group lifts: a new family.
ITERS4 = 500                  # annealing steps per group try in the 2x2 family
WIN4 = 6                      # candidate orders tried per pass in the 2x2 family
BUDGET4_START = 0.6
BUDGET4_CAP = 4.0
PHASE4_FRAC = 0.6             # share of the search time given to the 2x2 family


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
# Groups of order N: semidirect products Z_m x|_r Z_k (includes cyclic groups).
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
# Family 1: bi-Cayley graphs (one A-orbit, one B-orbit), as in the parent.
# A_x -- B_{x s} for s in S, |S| = d. Left multiplication is an automorphism.
# ----------------------------------------------------------------------------

def _unreached(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    if cur == 0:
        return S
    return None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a connection set with diameter <= D, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Family 2 (new): 2x2 base lifts over a group of order N.
#
# Four base vertices: A_0, A_1 (one side) and B_0, B_1 (other side).
# Each base pair (i, j) carries a set C_ij of group elements ("darts").
# Vertices are A_{i,x} and B_{j,y}; the lift has edges
#     A_{i,x} -- B_{j, x*g}   for g in C_ij.
# Row and column sums are both d, so the lift is d-regular and bipartite.
# With row sums a and d-a, the column sums are also d if C_01 and C_10 have
# sizes d-a and a. The graph has 4N vertices. Left multiplication is an
# automorphism that acts transitively on each of the four orbits, so the
# diameter is decided by BFS from the four identity vertices A_{0,e}, A_{1,e},
# B_{0,e}, B_{1,e}. Annealing moves one dart at a time.
# ----------------------------------------------------------------------------

def _unreached4(N, T, invs, cells, D):
    """Count (source, vertex) pairs not within distance D over the four identity sources."""
    outA = [[], []]
    outB = [[], []]
    for i in range(2):
        for j in range(2):
            for g in cells[i][j]:
                outA[i].append((j, g))
                outB[j].append((i, invs[g]))
    M = 4 * N
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(M)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < 2 * N:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in outA[i]:
                        v = 2 * N + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - 2 * N, N)
                    row = T[y]
                    for i, h in outB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += M - count
    return total


def _anneal4(N, T, invs, d, a, D, rng, iters, deadline):
    """Anneal the dart sets of a 2x2 base with row/col sums d (split a) to zero unreached pairs."""
    sizes = [[a, d - a], [d - a, a]]
    cells = [[rng.sample(range(N), sizes[i][j]) for j in range(2)] for i in range(2)]
    cur = _unreached4(N, T, invs, cells, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i, j = rng.randrange(2), rng.randrange(2)
        if not cells[i][j]:
            continue
        k = rng.randrange(len(cells[i][j]))
        c = rng.randrange(N)
        if c in cells[i][j]:
            continue
        old = cells[i][j][k]
        cells[i][j][k] = c
        v = _unreached4(N, T, invs, cells, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            cells[i][j][k] = old
    if cur == 0:
        return cells
    return None


def _attempt4(N, d, D, rng, deadline):
    """Try groups of order N for a 2x2 base lift with diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        a = rng.randint(1, d - 1)
        cells = _anneal4(N, T, invs, d, a, D, rng, ITERS4, deadline)
        if cells is not None:
            return T, cells
    return None


def _edges4(N, T, cells):
    """Edge list of the 2x2 lift: A_{i,x} = i*N + x, B_{j,y} = 2N + j*N + y."""
    edges = []
    for i in range(2):
        for j in range(2):
            for g in cells[i][j]:
                for x in range(N):
                    edges.append((i * N + x, 2 * N + j * N + T[x][g]))
    return edges


def _search4(d, D, rng, deadline, best_n):
    """Climb over orders N for the 2x2 family; return (n, edges) of the largest success, or None."""
    top = lib._moore_bound(d, D) // 4
    lo = max(d + 1, best_n // 4 + 1)
    budget = BUDGET4_START
    last = None
    while time.monotonic() < deadline and lo <= top:
        hi = min(top, lo + WIN4 - 1)
        cands = list(range(lo, hi + 1))
        rng.shuffle(cands)
        success = False
        for N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt4(N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, cells = res
            edges = _edges4(N, T, cells)
            last = (4 * N, edges)
            lo = N + 1          # climb: only larger orders are useful now
            success = True
            break
        if not success:
            if budget < BUDGET4_CAP:
                budget = min(BUDGET4_CAP, budget * 1.5)
    return last


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

    if D >= 2 and d >= 1:
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

    # Phase 1: 2x2 base lifts (four orbits), searched for orders above the current best.
    phase4_deadline = start + PHASE4_FRAC * (deadline - start)
    if time.monotonic() < phase4_deadline and lib._moore_bound(d, D) // 4 >= d + 1:
        res4 = _search4(d, D, rng, phase4_deadline, best_n)
        if res4 is not None:
            consider(*res4)

    # Phase 2: bi-Cayley (two orbits) search, as in the parent.
    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    top = min(Nmax, Nmax // 2 + 6)
    if top < d + 1:
        return best

    floor = max(d + 1, int(WINDOW_FRAC * top))
    bestN = best_n // 2
    budget = BUDGET_START

    while time.monotonic() < deadline:
        lo = max(floor, bestN + 1)
        cands = list(range(lo, top + 1))
        if not cands:
            break
        rng.shuffle(cands)
        success = False
        for N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            res = _attempt(N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)
            bestN = max(bestN, N)
            success = True
            break
        if not success:
            if budget < BUDGET_CAP:
                budget = min(BUDGET_CAP, budget * 1.5)
            elif floor > d + 1:
                floor -= 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
