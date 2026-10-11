import math
import random
import time

import lib

ITERS = 1500                  # annealing steps per (group, label assignment) try
T_HOT = 2.0                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.1                  # final annealing temperature
GROUPS_PER_TRY = 4            # groups tried for one base-matrix / order choice
DEADLINE_FRAC = 0.75          # fraction of time_limit used for search


# ----------------------------------------------------------------------------
# Safe fallbacks (validated before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-base bi-Cayley lifts.
#
# Group G of order N (semidirect Z_m x| Z_k). Base has k "A" vertices and k
# "B" vertices. Vertex A_i,x = i*N + x and B_j,y = (k+j)*N + y.
# Dart counts M[i][j] (k x k nonnegative integers, all row and column sums d)
# and label sets S[i][j] (subsets of G with |S[i][j]| = M[i][j]).
# Edges: A_i,x -- B_j, x*g for g in S[i][j].
#
# Each vertex has degree d, the graph is bipartite and simple. Left
# multiplication is an automorphism, so the k A-representatives and k
# B-representatives (vertices with coordinate e) are the only BFS sources
# needed for the diameter check.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, kk, r) with m*kk = N, giving Z_m x|_r Z_kk."""
    out = []
    for kk in range(1, N + 1):
        if N % kk:
            continue
        m = N // kk
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                out.append((m, kk, r))
    return out


def _dart_matrix(k, d, rng):
    """Random k x k nonnegative integer matrix with all row and column sums equal to d."""
    for _ in range(3000):
        M = [[0] * k for _ in range(k)]
        for i in range(k):
            for _ in range(d):
                M[i][rng.randrange(k)] += 1
        if all(sum(M[i][j] for i in range(k)) == d for j in range(k)):
            return M
    return None


def _unreached(N, k, T, ginv, S, D):
    """Count (source, vertex) pairs at distance > D, over the 2k representative sources."""
    V = 2 * k * N
    kN = k * N
    outA = [[(j, g) for j in range(k) for g in S[i][j]] for i in range(k)]
    outB = [[(i, ginv[g]) for i in range(k) for g in S[i][j]] for j in range(k)]
    sources = [i * N for i in range(k)] + [(k + j) * N for j in range(k)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < kN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in outA[i]:
                        v = (k + j) * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - kN, N)
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
        total += V - count
    return total


def _anneal(N, k, T, ginv, M, d, D, rng, deadline):
    """Simulated annealing over label sets to drive unreached pairs to zero."""
    S = [[rng.sample(range(N), M[i][j]) for j in range(k)] for i in range(k)]
    slots = [(i, j) for i in range(k) for j in range(k) if M[i][j] > 0]
    cur = _unreached(N, k, T, ginv, S, D)
    for it in range(ITERS):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        i, j = rng.choice(slots)
        idx = rng.randrange(M[i][j])
        c = rng.randrange(N)
        if c in S[i][j]:
            continue
        old = S[i][j][idx]
        S[i][j][idx] = c
        v = _unreached(N, k, T, ginv, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            S[i][j][idx] = old
    return S if cur == 0 else None


def _attempt(k, N, d, D, rng, deadline):
    """Try random dart matrices and groups of order N; return (T, S, M) on success."""
    M = _dart_matrix(k, d, rng)
    if M is None:
        return None
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:GROUPS_PER_TRY]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        ginv = [inv(g) for g in range(N)]
        S = _anneal(N, k, T, ginv, M, d, D, rng, deadline)
        if S is not None:
            return T, S, M
    return None


def _edges(N, k, T, S):
    """Build (n, edges) for the lift described by T and S."""
    edges = []
    for i in range(k):
        for j in range(k):
            for g in S[i][j]:
                for x in range(N):
                    edges.append((i * N + x, (k + j) * N + T[x][g]))
    return 2 * k * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + DEADLINE_FRAC * time_limit
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

    # Fallbacks, all validated by consider().
    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    spread = 3
    budget = 0.5
    fails = 0

    while time.monotonic() < deadline:
        k = rng.choice([1, 2, 2, 3])
        lo = best_n // (2 * k) + 1
        hi = moore // (2 * k)
        if lo > hi:
            k = 1
            lo = best_n // 2 + 1
            hi = moore // 2
            if lo > hi:
                break
        N = min(hi, lo + rng.randrange(spread + 1))

        now = time.monotonic()
        if now >= deadline:
            break
        att_deadline = min(deadline, now + budget)
        res = _attempt(k, N, d, D, rng, att_deadline)
        if res is None:
            fails += 1
            if fails % 3 == 0:
                budget *= 1.3
                spread += 2
            continue

        T, S, _M = res
        n, edges = _edges(N, k, T, S)
        consider(n, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
