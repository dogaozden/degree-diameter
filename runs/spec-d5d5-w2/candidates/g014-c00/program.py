import itertools
import math
import random
import time

import lib

INIT_BUDGET = 0.6        # seconds per annealing attempt at the start
BUDGET_CAP = 4.0         # cap on per-attempt seconds
WINDOW0 = 12             # number of candidate orders tried per pass
WINDOW_GROW = 6          # extra candidates added when budgets are maxed out
ANNEAL_ITERS = 4000      # annealing steps per attempt
T_HOT = 2.0
T_COLD = 0.1
A_MIN = 2                # base-graph half-size range (A-side vertices per base)
A_MAX = 5
DUP_PENALTY = 3


# ----------------------------------------------------------------------------
# Safe baseline families (always checked with lib.is_valid before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Voltage lifts over semidirect products Z_m x|_r Z_k with a SMALL base graph.
#
# Base graph: `a` A-vertices and `a` B-vertices. The d darts form d permutations
# pi_j of range(a); dart (u, pi_j(u), g) gives A-vertex (u, x) adjacent to
# B-vertex (pi_j(u), x*g) for every x in G. Every vertex then has degree d,
# the lift is bipartite, and its order is 2*a*N.
#
# Left multiplication by h acts as an automorphism, so only 2a BFS sources
# (one per base vertex) need to be checked.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _cost(a, N, D, T, invs, darts, gs):
    """Unreached (source, vertex) pairs over the 2a base sources, plus a penalty for repeated darts."""
    aN = a * N
    V = 2 * aN
    out = [[] for _ in range(a)]
    inn = [[] for _ in range(a)]
    keys = set()
    dup = 0
    for (u, v), g in zip(darts, gs):
        key = (u, v, g)
        if key in keys:
            dup += 1
        else:
            keys.add(key)
        out[u].append((aN + v * N, g))
        inn[v].append((u * N, invs[g]))

    total = 0
    for s in range(2 * a):
        src = s * N if s < a else aN + (s - a) * N
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for w in frontier:
                if w < aN:
                    u, x = divmod(w, N)
                    row = T[x]
                    for off, g in out[u]:
                        y = off + row[g]
                        if not seen[y]:
                            seen[y] = 1
                            nxt.append(y)
                else:
                    v, y = divmod(w - aN, N)
                    row = T[y]
                    for off, gi in inn[v]:
                        x = off + row[gi]
                        if not seen[x]:
                            seen[x] = 1
                            nxt.append(x)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - cnt
    return total + DUP_PENALTY * dup


def _edges(a, N, T, darts, gs):
    """Expand the base darts over the group into the full edge list."""
    aN = a * N
    edges = set()
    for (u, v), g in zip(darts, gs):
        for x in range(N):
            edges.add((u * N + x, aN + v * N + T[x][g]))
    return 2 * aN, sorted(edges)


def _attempt(a, N, d, D, rng, deadline, budget):
    """One randomized annealing attempt for lift order N with base size a. Returns (n, edges) or None."""
    groups = _groups(N)
    if not groups:
        return None
    m, k, r = rng.choice(groups)
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]

    darts = []
    for _ in range(d):
        perm = list(range(a))
        rng.shuffle(perm)
        darts.extend((u, perm[u]) for u in range(a))
    L = len(darts)

    gs = [rng.randrange(N) for _ in range(L)]
    cur = _cost(a, N, D, T, invs, darts, gs)
    end = min(deadline, time.monotonic() + budget)

    for it in range(ANNEAL_ITERS):
        if cur == 0 or time.monotonic() > end:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ANNEAL_ITERS)
        i = rng.randrange(L)
        g_new = rng.randrange(N)
        if g_new == gs[i]:
            continue
        old = gs[i]
        gs[i] = g_new
        c = _cost(a, N, D, T, invs, darts, gs)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            gs[i] = old

    if cur == 0:
        return _edges(a, N, T, darts, gs)
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
            return True
        return False

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    # Safe fallbacks.
    if D >= 2 and d >= 1:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3 and d >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    # Main search: small-base voltage lifts over non-cyclic groups, aiming above best_n.
    moore = lib._moore_bound(d, D)
    cands = []
    for a in range(A_MIN, A_MAX + 1):
        Nmin = max(2, best_n // (2 * a) + 1)
        Nmax = moore // (2 * a)
        for N in range(Nmin, Nmax + 1):
            cands.append((2 * a * N, a, N))
    cands.sort()

    banned = set()
    B = INIT_BUDGET
    W = WINDOW0
    while time.monotonic() < deadline:
        pending = [c for c in cands if c[0] > best_n and c[0] not in banned]
        if not pending:
            break
        window = pending[:W]
        success = False
        for n_cand, a, N in window:
            if time.monotonic() >= deadline:
                break
            res = _attempt(a, N, d, D, rng, deadline, B)
            if res is None:
                continue
            n2, e2 = res
            if consider(n2, e2):
                success = True
                break
            banned.add(n2)
        if not success:
            if B < BUDGET_CAP:
                B = min(BUDGET_CAP, B * 1.6)
            else:
                W += WINDOW_GROW

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
