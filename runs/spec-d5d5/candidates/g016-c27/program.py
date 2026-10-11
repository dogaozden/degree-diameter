import math
import random
import time
from itertools import islice

import lib

ITERS = 400      # annealing steps per (group, count matrix) try
MAX_N = 400      # largest group order considered (keeps multiplication tables small)
MAX_P = 3        # base vertices per side in the voltage lift
WINDOW = 8       # (total, p, N) candidates tried per pass


# ----------------------------------------------------------------------------
# Safe baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Non-bi-Cayley family: voltage lifts with p base vertices per side.
#
# Base graph: p "A" vertices and p "B" vertices. The count matrix C has row and
# column sums d (a sum of d random permutation matrices). Each cell (i, j) with
# C[i][j] = c carries c distinct voltages g in a group G of order N. The lift has
# vertices A(i, x) = i*N + x and B(j, y) = p*N + j*N + y, with edges
# A(i, x) -- B(j, x*g) for every dart (i, j, g). Every vertex has degree d.
# Left multiplication is an automorphism, but the check below tests all vertices
# directly, so that symmetry is not relied on.
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


def _count_matrix(p, d, rng):
    """p x p nonnegative integer matrix with all row and column sums equal to d."""
    C = [[0] * p for _ in range(p)]
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        for i in range(p):
            C[i][perm[i]] += 1
    return C


def _nbrs(darts, N, p, T):
    """Adjacency lists of the lift described by darts [i, j, g]."""
    V = 2 * p * N
    Bo = p * N
    nbr = [[] for _ in range(V)]
    for i, j, g in darts:
        base_b = Bo + j * N
        for x in range(N):
            a = i * N + x
            b = base_b + T[x][g]
            nbr[a].append(b)
            nbr[b].append(a)
    return nbr


def _cost(nbr, V, D):
    """Number of ordered vertex pairs at distance more than D (0 means diameter <= D)."""
    reach = [1 << v for v in range(V)]
    for _ in range(D):
        new = []
        for v in range(V):
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(V - r.bit_count() for r in reach)


def _search(p, N, d, D, rng, deadline):
    """Anneal voltages over random groups of order N until diameter <= D, or give up at deadline."""
    V = 2 * p * N
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        C = _count_matrix(p, d, rng)
        darts = []
        for i in range(p):
            for j in range(p):
                for g in rng.sample(range(N), C[i][j]):
                    darts.append([i, j, g])
        cur = _cost(_nbrs(darts, N, p, T), V, D)
        for it in range(ITERS + 1):
            if cur == 0:
                return N, p, [tuple(x) for x in darts], T
            if it == ITERS or time.monotonic() > deadline:
                break
            idx = rng.randrange(len(darts))
            i, j, g = darts[idx]
            g2 = rng.randrange(N)
            if g2 == g or any(a == i and b == j and c == g2 for a, b, c in darts):
                continue
            darts[idx][2] = g2
            v = _cost(_nbrs(darts, N, p, T), V, D)
            temp = max(0.3, 3.0 * (1.0 - it / ITERS))
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                darts[idx][2] = g
    return None


def _edges(N, p, darts, T):
    """Edge list of the voltage lift with vertices A(i,x) = i*N+x and B(j,y) = p*N+j*N+y."""
    Bo = p * N
    return [(i * N + x, Bo + j * N + T[x][g]) for i, j, g in darts for x in range(N)]


def _candidates(lo, hi, d):
    """(total, p, N) with total = 2*p*N in [lo, hi], in ascending order of total."""
    for total in range(lo, hi + 1):
        if total % 2:
            continue
        for p in range(1, MAX_P + 1):
            if total % (2 * p):
                continue
            N = total // (2 * p)
            if d <= N <= MAX_N:
                yield total, p, N


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed)
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

    # Safe fallback: K_{d,d} (diameter 2), or a single edge when d = 1.
    consider(*lib.haar_graph(d, range(d)))
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    moore = lib._moore_bound(d, D)
    budget = 1.0
    while time.monotonic() < deadline:
        cands = list(islice(_candidates(best[0] + 1, moore, d), WINDOW))
        if not cands:
            break
        improved = False
        for total, p, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _search(p, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            N_, p_, darts, T = res
            before = best[0]
            consider(2 * p_ * N_, _edges(N_, p_, darts, T))
            if best[0] > before:
                improved = True
                break
        if not improved:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
