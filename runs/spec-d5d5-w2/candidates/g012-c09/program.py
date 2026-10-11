"""Construction search for bipartite graphs with max degree d and diameter D.

Families, in order of use:
  1. Small closed-form baselines (Haar graph, PG(2,q) incidence, W(q) quadrangle).
  2. Two-vertex-per-side voltage lifts over semidirect products Z_m x| Z_k
     (new in this version). Each side has 2 base vertices, so the graph has
     4N vertices. Darts from A_i to B_j form a 2x2 count matrix with all row and
     column sums d. Annealing chooses group voltages until every pair is within
     distance D. Only the identity sources of the four base vertices need checking,
     since left multiplication is an automorphism.
  3. Bi-Cayley graphs (one base vertex per side), kept from the parent as a fallback.

Every candidate is checked with lib.is_valid before it is kept, so the returned
graph is always valid.
"""
import itertools
import math
import random
import time

import lib

# Bi-Cayley (one base vertex per side) search parameters.
ITERS = 600
T_HOT = 1.5
T_COLD = 0.15
MAX_GROUPS_PER_ATTEMPT = 12
WINDOW_FRAC = 0.95
BUDGET_START = 0.4
BUDGET_CAP = 3.0

# Two-vertex-per-side lift search parameters.
LIFT_ITERS = 250
LIFT_BUDGET_START = 0.8
LIFT_BUDGET_CAP = 4.0
LIFT_FRAC = 0.55   # share of the search time given to the lift family
LIFT_WIDTH = 30    # initial width of the order window above the current floor


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
# Shared group helpers.
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
# Two-vertex-per-side voltage lifts (new family).
#
# Base vertices: A_0, A_1 (side A) and B_0, B_1 (side B).
# Vertex ids: A_i, x -> i*N + x ; B_j, y -> (2+j)*N + y.
# Darts: for each (i, j), H[i][j] is a set of M[i][j] distinct group elements h,
# giving edges A_i,x -- B_j, x*h for all x. Degree of every vertex equals d when
# the count matrix M has all row and column sums d.
# ----------------------------------------------------------------------------

def _lift_matrices(d):
    """Dart-count matrices with row and column sums d.

    Up to relabelling B_0 and B_1, the 2x2 matrices with positive entries and
    row/column sums d are [[x, d-x], [d-x, x]]. Taking 1 <= x <= d//2 covers them.
    """
    if d < 2:
        return []
    return [[[x, d - x], [d - x, x]] for x in range(1, d // 2 + 1)]


def _lift_unreached(N, T, nbrA, nbrB, D):
    """Count (source, vertex) pairs not within distance D, for the four base identities."""
    V = 4 * N
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                b, r = divmod(u, N)
                row = T[r]
                if b < 2:
                    for j, h in nbrA[b]:
                        v = (2 + j) * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    for i, hi in nbrB[b - 2]:
                        v = i * N + row[hi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _lift_cost(N, T, invs, H, D):
    """Unreached-pair count for the dart sets H."""
    nbrA = [[] for _ in range(2)]
    nbrB = [[] for _ in range(2)]
    for i in range(2):
        for j in range(2):
            for h in H[i][j]:
                nbrA[i].append((j, h))
                nbrB[j].append((i, invs[h]))
    return _lift_unreached(N, T, nbrA, nbrB, D)


def _lift_anneal(N, T, invs, M, D, rng, iters, deadline):
    """Anneal the dart sets for count matrix M. Returns H with zero cost, or None."""
    H = [[rng.sample(range(N), M[i][j]) for j in range(2)] for i in range(2)]
    cells = [(i, j) for i in range(2) for j in range(2) if M[i][j] > 0]
    cur = _lift_cost(N, T, invs, H, D)
    for it in range(iters):
        if cur == 0:
            return H
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i, j = rng.choice(cells)
        cell = H[i][j]
        t = rng.randrange(len(cell))
        c = rng.randrange(N)
        if c in cell:
            continue
        old = cell[t]
        cell[t] = c
        v = _lift_cost(N, T, invs, H, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            cell[t] = old
    if cur == 0:
        return H
    return None


def _lift_attempt(N, d, D, rng, deadline):
    """Try groups of order N and count matrices until one lift has diameter <= D."""
    mats = _lift_matrices(d)
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        rng.shuffle(mats)
        for M in mats:
            H = _lift_anneal(N, T, invs, M, D, rng, LIFT_ITERS, deadline)
            if H is not None:
                return T, H
    return None


def _lift_edges(N, T, H):
    """Edge list of the lift: A_i,x -- B_j,(x*h) for every dart (i, j, h)."""
    edges = []
    for i in range(2):
        for j in range(2):
            for h in H[i][j]:
                for x in range(N):
                    edges.append((i * N + x, (2 + j) * N + T[x][h]))
    return 4 * N, edges


def _search_lift(d, D, rng, deadline, best_n):
    """Search lifts of increasing order 4N above best_n. Returns (n, edges) or None."""
    top = lib.moore_bound(d, D) // 4
    lo = max(best_n // 4 + 1, 2)
    if d < 2 or top < lo:
        return None
    width = LIFT_WIDTH
    budget = LIFT_BUDGET_START
    found = None
    while time.monotonic() < deadline and lo <= top:
        cands = list(range(lo, min(top, lo + width) + 1))
        rng.shuffle(cands)
        success = False
        for N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _lift_attempt(N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, H = res
            n, edges = _lift_edges(N, T, H)
            if lib.is_valid(n, edges, d, D):
                found = (n, edges)
                lo = N + 1
                success = True
                break
        if not success:
            if budget < LIFT_BUDGET_CAP:
                budget = min(LIFT_BUDGET_CAP, budget * 1.5)
            else:
                width = max(1, width // 2)
    return found


# ----------------------------------------------------------------------------
# Bi-Cayley search over semidirect products (parent family, kept as fallback).
#
# Vertices A_x and B_y (x, y in G). Edge A_x -- B_{x s} for s in S, |S| = d.
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
    """Try groups of order N until one yields a connection set with diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _search_bicayley(d, D, rng, deadline, best_n):
    """Parent's bi-Cayley window search. Returns a valid (n, edges) or None."""
    Nmax = lib.moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + 6)
    if top < d + 1:
        return None
    floor = max(d + 1, int(WINDOW_FRAC * top))
    bestN = best_n // 2
    budget = BUDGET_START
    found = None
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
            if lib.is_valid(2 * N, edges, d, D):
                found = (2 * N, edges)
                bestN = max(bestN, N)
                success = True
                break
        if not success:
            if budget < BUDGET_CAP:
                budget = min(BUDGET_CAP, budget * 1.5)
            elif floor > d + 1:
                floor -= 1
    return found


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

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

    # Family 2: two-vertex-per-side lifts, the bold new construction.
    now = time.monotonic()
    lift_deadline = now + LIFT_FRAC * max(0.0, deadline - now)
    lift = _search_lift(d, D, rng, lift_deadline, best_n)
    if lift is not None:
        consider(*lift)

    # Family 3: bi-Cayley search (parent), using the remaining time.
    bi = _search_bicayley(d, D, rng, deadline, best_n)
    if bi is not None:
        consider(*bi)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
