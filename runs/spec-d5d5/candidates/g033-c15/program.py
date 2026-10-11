import math
import random
import time

import lib

ITERS = 1000                  # annealing steps per attempt
T_HOT = 1.2                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.1                  # final annealing temperature
K_CHOICES = (2, 3)            # base orbits per side for block-voltage lifts
ATTEMPT_BUDGET = 3.0          # seconds allowed per (group, block matrix) attempt


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
# New construction: block-voltage lifts over a finite group.
#
# Base graph: k "A" orbits and k "B" orbits (2k base vertices). Each group
# element x gives vertices A_{i,x} and B_{j,y}. For each block (i, j) we pick a
# set S_ij of group elements of size M[i][j], and join A_{i,x} to B_{j,x s}
# for s in S_ij. The block matrix M has every row and column summing to d
# (built as a sum of d random permutation matrices), so every vertex has degree
# exactly d. The lift has 2kN vertices, so k = 2 or 3 targets orders that
# bi-Cayley (k = 1) search cannot reach at this degree.
#
# Left multiplication is an automorphism, so the diameter is decided by BFS
# from the k A-representatives A_{i,e} and k B-representatives B_{j,e}.
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


def _random_block_matrix(k, d, rng):
    """k x k nonnegative integer matrix with all row and column sums equal to d."""
    M = [[0] * k for _ in range(k)]
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            M[i][perm[i]] += 1
    return M


def _unreached(N, k, T, invs, sets, D):
    """Count (source, vertex) pairs at distance more than D, over the 2k orbit representatives."""
    K = k * N
    V = 2 * K
    rowsA = [[(j, sets[i][j]) for j in range(k) if sets[i][j]] for i in range(k)]
    colsB = [[(i, [invs[s] for s in sets[i][j]]) for i in range(k) if sets[i][j]]
             for j in range(k)]
    sources = [i * N for i in range(k)] + [K + j * N for j in range(k)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < K:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, S in rowsA[i]:
                        base = K + j * N
                        for s in S:
                            v = base + row[s]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                else:
                    j, y = divmod(u - K, N)
                    row = T[y]
                    for i, H in colsB[j]:
                        base = i * N
                        for h in H:
                            v = base + row[h]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(N, k, T, invs, M, D, rng, iters, deadline):
    """Anneal the block connection sets until every source reaches all vertices within D."""
    blocks = [(i, j) for i in range(k) for j in range(k) if M[i][j] > 0]
    sets = [[[] for _ in range(k)] for _ in range(k)]
    for i, j in blocks:
        sets[i][j] = rng.sample(range(N), M[i][j])
    cur = _unreached(N, k, T, invs, sets, D)
    if cur == 0:
        return sets
    for it in range(iters):
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i, j = rng.choice(blocks)
        idx = rng.randrange(len(sets[i][j]))
        c = rng.randrange(N)
        if c in sets[i][j]:
            continue
        old = sets[i][j][idx]
        sets[i][j][idx] = c
        v = _unreached(N, k, T, invs, sets, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
            if cur == 0:
                return sets
        else:
            sets[i][j][idx] = old
    return None


def _attempt(N, k, d, D, rng, deadline):
    """Try one random group of order N with one random block matrix; return a lift or None."""
    groups = _groups(N)
    if not groups:
        return None
    m, kk, r = rng.choice(groups)
    _, mul, inv = lib.semidirect_group(m, kk, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    M = _random_block_matrix(k, d, rng)
    sets = _anneal(N, k, T, invs, M, D, rng, ITERS, deadline)
    if sets is None:
        return None
    return N, k, T, sets


def _lift_edges(N, k, T, sets):
    """Edge list of the block-voltage lift; vertex A_{i,x} = i*N + x, B_{j,y} = k*N + j*N + y."""
    K = k * N
    edges = []
    for i in range(k):
        for j in range(k):
            for s in sets[i][j]:
                for x in range(N):
                    edges.append((i * N + x, K + j * N + T[x][s]))
    return edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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
        return best

    moore = lib._moore_bound(d, D)
    fails = 0
    while time.monotonic() < deadline:
        k = rng.choice(K_CHOICES)
        n_min = best_n // (2 * k) + 1
        n_max = moore // (2 * k)
        if n_min > n_max:
            # This k cannot beat the current best; try the other.
            if all(best_n // (2 * kk) + 1 > moore // (2 * kk) for kk in K_CHOICES):
                break
            continue
        spread = min(n_max, n_min + 4 + fails // 6)
        N = rng.randint(n_min, spread)
        now = time.monotonic()
        att_deadline = min(deadline, now + ATTEMPT_BUDGET)
        res = _attempt(N, k, d, D, rng, att_deadline)
        if res is None:
            fails += 1
            continue
        N, k, T, sets = res
        consider(2 * k * N, _lift_edges(N, k, T, sets))
        fails = 0

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
