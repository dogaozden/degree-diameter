import math
import random
import time

import lib

ITERS = 500                   # annealing steps per group try
T_HOT = 1.5                   # initial temperature (in unreached-pair units)
T_COLD = 0.15                 # final temperature
GROUPS_PER_N = 10             # groups tried per (orbit count, order) attempt
PHASE1_FRAC = 0.35            # fraction of the budget spent on the one-orbit phase


# ----------------------------------------------------------------------------
# Baseline families (always validated before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit bi-Cayley lifts.
#
# Base graph: s "A" vertices and s "B" vertices. Each base dart (i, j, g) joins
# A(i, x) to B(j, x*g) for every x in the group G (order N). The base multigraph
# has s*d darts split so that every base vertex has degree d (matrix M with
# row and column sums d). Left multiplication by h is an automorphism, so
# eccentricities only need sources A(i, identity) and B(j, identity).
#
# s = 1 is an ordinary bi-Cayley graph on 2N vertices. s = 2 gives 4N vertices,
# a genuinely different family whose orders are not twice a group order.
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


def _cost(N, s, T, darts, D):
    """Total (source, vertex) pairs not within distance D over the 2*s orbit representatives."""
    V = 2 * s * N
    adj = [[] for _ in range(V)]
    for i, j, g in darts:
        bj = s * N + j * N
        ai = i * N
        for x in range(N):
            a = ai + x
            b = bj + T[x][g]
            adj[a].append(b)
            adj[b].append(a)
    sources = [i * N for i in range(s)] + [s * N + j * N for j in range(s)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        cnt = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - cnt
    return total


def _anneal(N, s, T, D, counts, rng, iters, deadline):
    """Anneal the group elements on the darts until every base-orbit pair is within D.

    Returns the dart list (i, j, g) on success, otherwise None.
    """
    darts = []
    for i, j, n in counts:
        for g in rng.sample(range(N), n):
            darts.append((i, j, g))
    cur = _cost(N, s, T, darts, D)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        k = rng.randrange(len(darts))
        i, j, g = darts[k]
        g2 = rng.randrange(N)
        if g2 == g or any(a == i and b == j and c == g2 for a, b, c in darts):
            continue
        old = darts[k]
        darts[k] = (i, j, g2)
        v = _cost(N, s, T, darts, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[k] = old
    return darts if cur == 0 else None


def _attempt(N, d, D, s, rng, deadline):
    """Try groups of order N for an s-orbit lift; return (T, darts) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_N]:
        if time.monotonic() > deadline:
            return None
        if s == 1:
            counts = [(0, 0, d)]
        else:
            p = rng.randrange(1, d)  # both 1..d-1 keep every base entry positive
            counts = [(0, 0, p), (0, 1, d - p), (1, 0, d - p), (1, 1, p)]
        counts = [c for c in counts if c[2] > 0]
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        darts = _anneal(N, s, T, D, counts, rng, ITERS, deadline)
        if darts is not None:
            return T, darts
    return None


def _edges(N, s, T, darts):
    """Edge list of the lift: A(i,x) -- B(j, x*g) for every dart (i, j, g)."""
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, s * N + j * N + T[x][g]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.8 * time_limit
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

    if d < 2 or D < 2:
        if not lib.is_valid(best[0], best[1], d, D):
            return 1, []
        return best

    bound = lib._moore_bound(d, D)

    # Phase 1: one-orbit bi-Cayley (secures the record-level order).
    # Phase 2: two-orbit base (4N vertices), the more different construction.
    phases = [
        (1, start + PHASE1_FRAC * time_limit),
        (2, end),
    ]
    for s, pend in phases:
        if time.monotonic() >= pend:
            continue
        Nmax = bound // (2 * s)
        N = max(d + 1, best_n // (2 * s) + 1, int(0.45 * Nmax))
        budget = 1.0
        while N <= Nmax and time.monotonic() < pend:
            now = time.monotonic()
            att_deadline = min(pend, now + budget)
            res = _attempt(N, d, D, s, rng, att_deadline)
            if res is None:
                budget *= 2  # retry the same order with more time
                continue
            T, darts = res
            consider(2 * s * N, _edges(N, s, T, darts))
            N += 1
            budget = 1.0

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
