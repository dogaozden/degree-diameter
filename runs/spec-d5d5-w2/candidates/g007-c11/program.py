import itertools
import math
import random
import time

import lib

ITERS = 450          # annealing steps per (group, multiplicity matrix) try
T_HOT = 2.0          # initial annealing temperature (unreached-pair units)
T_COLD = 0.1         # final annealing temperature
MAX_GROUPS = 8       # groups tried per attempt
BUDGET_START = 2.0   # seconds per (a, N) attempt at first
BUDGET_CAP = 6.0     # cap on per-attempt seconds
WINDOW_START = 4     # search this many N values below the top of the range
A_CHOICES = [2, 3, 4, 5, 6, 2, 3, 4, 5, 6, 1]


# ----------------------------------------------------------------------------
# Fallback families (always checked with lib.is_valid before use).
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k (cyclic when k = 1)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _random_mult(a, d, rng):
    """a x a nonnegative integer matrix with all row and column sums d (sum of d random permutations)."""
    M = [[0] * a for _ in range(a)]
    for _ in range(d):
        perm = list(range(a))
        rng.shuffle(perm)
        for i in range(a):
            M[i][perm[i]] += 1
    return M


# ----------------------------------------------------------------------------
# Multi-base-vertex voltage lifts over semidirect groups.
#
# Base: a A-vertices and a B-vertices, a d-regular bipartite multigraph with
# multiplicity matrix M. Each base dart (i, j, g) gives the lifted edges
# A_{i,x} -- B_{j, x*g} for all x in G. Left multiplication by G is an
# automorphism that is transitive on each fibre, so one BFS per base vertex
# determines the diameter. This differs from the single-pair bi-Cayley search.
# ----------------------------------------------------------------------------

def _cost(a, N, D, T, adjA, adjB):
    """Total number of (base source, vertex) pairs at distance > D, over all 2a base sources."""
    base = a * N
    V = 2 * base
    srcs = [i * N for i in range(a)] + [base + j * N for j in range(a)]
    total = 0
    for src in srcs:
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
                    for j, g in adjA[i]:
                        v = base + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - base, N)
                    row = T[y]
                    for i, h in adjB[j]:
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


def _anneal(a, N, D, T, invs, darts, rng, deadline):
    """Anneal voltages (darts = list of [i, j, g]) so every base source reaches all vertices within D.

    Within one (i, j) cell the voltages stay distinct, so the lift is simple
    and exactly d-regular.
    """
    def costof(ds):
        adjA = [[] for _ in range(a)]
        adjB = [[] for _ in range(a)]
        for i, j, g in ds:
            adjA[i].append((j, g))
            adjB[j].append((i, invs[g]))
        return _cost(a, N, D, T, adjA, adjB)

    cur = costof(darts)
    for it in range(ITERS):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        t = rng.randrange(len(darts))
        i, j, g = darts[t]
        used = {gg for (ii, jj, gg) in darts if ii == i and jj == j}
        if len(used) >= N:
            continue
        new = rng.randrange(N)
        while new in used:
            new = rng.randrange(N)
        darts[t] = [i, j, new]
        v = costof(darts)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[t] = [i, j, g]
    return darts if cur == 0 else None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N with random multiplicity matrices until a lift has diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        M = _random_mult(a, d, rng)
        if max(max(row) for row in M) > N:
            continue
        darts = []
        for i in range(a):
            for j in range(a):
                if M[i][j]:
                    for g in rng.sample(range(N), M[i][j]):
                        darts.append([i, j, g])
        res = _anneal(a, N, D, T, invs, darts, rng, deadline)
        if res is not None:
            return T, res
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.5
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

    # Exact record case for D = 3: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    consider(*lib.haar_graph(d, range(d)))

    if d < 2 or D < 2:
        return best

    moore = lib.moore_bound(d, D)
    window = WINDOW_START
    budget = BUDGET_START

    while time.monotonic() < deadline:
        # Feasible choices of a: need 2*a*N > best_n with N <= moore / (2a).
        feasible = [a for a in A_CHOICES if best_n // (2 * a) + 1 <= moore // (2 * a)]
        if not feasible:
            break
        a = rng.choice(feasible)
        hi = moore // (2 * a)
        lo = best_n // (2 * a) + 1
        win = max(1, min(window, hi - lo + 1))
        N = max(lo, hi - rng.randrange(win))
        N = min(N, hi)
        if N < d:
            continue

        now = time.monotonic()
        if now >= deadline:
            break
        att_deadline = min(deadline, now + budget)
        res = _attempt(a, N, d, D, rng, att_deadline)
        if res is None:
            window = min(window + 1, max(1, hi - lo + 1))
            budget = min(BUDGET_CAP, budget * 1.1)
            continue

        T, darts = res
        base = a * N
        edges = []
        for i, j, g in darts:
            for x in range(N):
                edges.append((i * N + x, base + j * N + T[x][g]))
        before = best_n
        consider(2 * base, edges)
        if best_n > before:
            window = WINDOW_START

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
