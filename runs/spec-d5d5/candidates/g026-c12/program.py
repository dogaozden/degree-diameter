import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per (k, N) attempt
ITERS = 1500                  # annealing steps per (group, count matrix) try
T_HOT = 1.2                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.1                  # final annealing temperature
ORBIT_COUNTS = (1, 2, 3)      # numbers of A-orbits (= B-orbits) to try
WINDOW = 10                   # orders tried per orbit count above the current best

# Multi-orbit bi-Cayley lifts (new in this version).
#
# The parent only used one A-orbit and one B-orbit: vertices A_x, B_y over a
# group G, with A_x ~ B_{x s} for s in S (|S| = d). Here there are k A-orbits
# and k B-orbits, so the graph has 2kN vertices A_{i,x}, B_{j,y}. For each
# orbit pair (i, j) there is a connection set S[i][j] of size C[i][j], where the
# count matrix C has all row and column sums equal to d. Then
#     A_{i,x} ~ B_{j, x s}  for s in S[i][j].
# Left multiplication by G preserves all edges and is transitive on each orbit,
# so the diameter is decided by BFS from one source per orbit (A_{i,0}, B_{j,0}).
# The count matrix is a sum of d random permutation matrices. This lets the
# degree budget split across orbits, which the k = 1 case cannot do.


# ----------------------------------------------------------------------------
# Baseline family (fast, always valid when it passes lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit bi-Cayley search over semidirect products Z_m x| Z_k of order N.
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


def _random_counts(k, d, rng):
    """k x k nonnegative integer matrix with all row and column sums equal to d.

    It is a sum of d random permutation matrices, so every row and column sums to d.
    """
    M = [[0] * k for _ in range(k)]
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            M[i][perm[i]] += 1
    return M


def _build_adj(k, S, invs):
    """Per A-orbit out-lists of (j, s) and per B-orbit in-lists of (i, s^-1)."""
    out = [[] for _ in range(k)]
    inn = [[] for _ in range(k)]
    for i in range(k):
        for j in range(k):
            for s in S[i][j]:
                out[i].append((j, s))
                inn[j].append((i, invs[s]))
    return out, inn


def _cost(N, k, T, invs, S, D):
    """Total unreached (source, vertex) pairs, summed over one source per orbit."""
    out, inn = _build_adj(k, S, invs)
    kN = k * N
    V = 2 * kN
    total = 0
    sources = [i * N for i in range(k)] + [kN + j * N for j in range(k)]
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        reached = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < kN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, s in out[i]:
                        v = kN + j * N + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - kN, N)
                    row = T[y]
                    for i, si in inn[j]:
                        v = i * N + row[si]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            reached += len(nxt)
            frontier = nxt
            if reached == V:
                break
        total += V - reached
    return total


def _anneal(N, k, T, invs, C, D, rng, iters, deadline):
    """Anneal the connection sets S[i][j] (sizes fixed by C) to zero unreached pairs."""
    S = [[[] for _ in range(k)] for _ in range(k)]
    pairs = []
    for i in range(k):
        for j in range(k):
            c = C[i][j]
            if c:
                S[i][j] = rng.sample(range(N), c)
                pairs.append((i, j))
    if not pairs:
        return None
    cur = _cost(N, k, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i, j = rng.choice(pairs)
        lst = S[i][j]
        p = rng.randrange(len(lst))
        c = rng.randrange(N)
        if c in lst:
            continue
        old = lst[p]
        lst[p] = c
        v = _cost(N, k, T, invs, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            lst[p] = old
    return S if cur == 0 else None


def _attempt(N, k, d, D, rng, deadline):
    """Try groups of order N with random count matrices until one yields diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        C = _random_counts(k, d, rng)
        S = _anneal(N, k, T, invs, C, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _edges_from(N, k, T, S):
    """Edge list of the k-orbit bi-Cayley graph: A_{i,x} = i*N + x, B_{j,y} = kN + j*N + y."""
    kN = k * N
    edges = []
    for i in range(k):
        for x in range(N):
            for j in range(k):
                row = T[x]
                for s in S[i][j]:
                    edges.append((i * N + x, kN + j * N + row[s]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.8 * time_limit, time_limit - 3.0))
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

    # Pool of (vertex count, orbit count k, group order N, per-candidate budget).
    pool = []
    for k in ORBIT_COUNTS:
        Nmax = moore // (2 * k)
        lo = max(best_n // (2 * k) + 1, d)
        for N in range(lo, min(Nmax, lo + WINDOW) + 1):
            n_tot = 2 * k * N
            if best_n < n_tot <= moore:
                pool.append([n_tot, k, N, 0.5])
    pool.sort()

    while time.monotonic() < deadline:
        pool = [e for e in pool if e[0] > best_n]
        if not pool:
            break
        for entry in pool:
            if time.monotonic() >= deadline:
                break
            n_tot, k, N, budget = entry
            att_deadline = min(deadline, time.monotonic() + budget)
            res = _attempt(N, k, d, D, rng, att_deadline)
            if res is None:
                entry[3] *= 2
                continue
            T, S = res
            consider(2 * k * N, _edges_from(N, k, T, S))
            break  # pool changed (best improved); recompute it

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
