import math
import random
import time

import lib

T_HOT = 2.0        # initial annealing temperature (in unreached-pair units)
T_COLD = 0.2       # final annealing temperature
ITERS = 800        # annealing steps per (group, base structure) try
MAX_GROUPS = 10    # groups tried per (orbits, order) candidate within one attempt
WINDOW0 = 40       # initial window of target sizes above the current best
MAX_ORBITS = 4     # maximum number of A-orbits (and B-orbits) in a lift


# ----------------------------------------------------------------------------
# Groups: metacyclic Z_m x|_r Z_kk of order N (identity is element 0).
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, kk, r) with m*kk = N."""
    out = []
    for kk in range(1, N + 1):
        if N % kk:
            continue
        m = N // kk
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                out.append((m, kk, r))
    return out


def _tables(N, m, kk, r):
    """Multiplication table T[x][g] = x*g and inverse table for the group."""
    _, mul, inv = lib.semidirect_group(m, kk, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    return T, invs


# ----------------------------------------------------------------------------
# NEW: multi-orbit voltage lifts with a random d-regular bipartite base.
#
# Base: k "A-orbits" and k "B-orbits". Base multigraph M (k x k, all row and
# column sums d) is a sum of d random permutation matrices, so each base vertex
# has exactly d darts. Each dart (i, j) carries a group element g and gives the
# edges (A_i, x) -- (B_j, x*g) for all x in G. Total order 2*k*N, degree <= d.
#
# Left multiplication by h is an automorphism, so eccentricities depend only on
# the base vertex; BFS from one source per orbit (2k sources) decides diameter.
# ----------------------------------------------------------------------------

def _random_base(k, d, rng):
    """Return the list of darts (i, j), k*d of them, grouped by i in blocks of d."""
    M = [[0] * k for _ in range(k)]
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            M[i][p[i]] += 1
    darts = []
    for i in range(k):
        row = []
        for j in range(k):
            row += [j] * M[i][j]
        rng.shuffle(row)
        for j in row:
            darts.append((i, j))
    return darts


def _unreached(N, k, T, invs, darts, gs, D):
    """Number of (source, vertex) pairs not within distance D, over one source per orbit."""
    Aadj = [[] for _ in range(k)]
    Badj = [[] for _ in range(k)]
    for (i, j), g in zip(darts, gs):
        Aadj[i].append((j, g))
        Badj[j].append((i, invs[g]))
    KN = k * N
    V = 2 * KN
    total = 0
    sources = [i * N for i in range(k)] + [KN + j * N for j in range(k)]
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < KN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in Aadj[i]:
                        v = KN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - KN, N)
                    row = T[y]
                    for i, h in Badj[j]:
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


def _anneal(N, k, T, invs, darts, D, rng, deadline):
    """Anneal the dart voltages to zero unreached pairs; return voltages or None."""
    gs = [rng.randrange(N) for _ in darts]
    cur = _unreached(N, k, T, invs, darts, gs, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        idx = rng.randrange(len(darts))
        newg = rng.randrange(N)
        if newg == gs[idx]:
            continue
        old = gs[idx]
        gs[idx] = newg
        v = _unreached(N, k, T, invs, darts, gs, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[idx] = old
    return gs if cur == 0 else None


def _lift_edges(N, k, T, darts, gs):
    """Edge list of the lift: A-orbit i is ids i*N..., B-orbit j is ids k*N + j*N..."""
    KN = k * N
    edges = set()
    for (i, j), g in zip(darts, gs):
        for x in range(N):
            edges.add((i * N + x, KN + j * N + T[x][g]))
    return 2 * KN, sorted(edges)


def _attempt(N, k, d, D, rng, deadline):
    """Try groups of order N for a k-orbit lift; return (n, edges) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        T, invs = _tables(N, m, kk, r)
        darts = _random_base(k, d, rng)
        gs = _anneal(N, k, T, invs, darts, D, rng, deadline)
        if gs is not None:
            return _lift_edges(N, k, T, darts, gs)
    return None


# ----------------------------------------------------------------------------
# Baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (2, [(0, 1)])   # K2: valid for any d >= 1, D >= 1
    best_n = 2

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 1:
        return best

    # Record-matching case for D = 3.
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
    window = WINDOW0
    budget = 0.3

    while time.monotonic() < deadline:
        if best_n >= moore:
            break
        hi = min(moore, best_n + window)
        cands = []
        for k in range(1, MAX_ORBITS + 1):
            for N in range(2, hi // (2 * k) + 1):
                size = 2 * k * N
                if best_n < size <= hi:
                    cands.append((size, k, N))
        if not cands:
            window *= 2
            continue
        cands.sort()

        progress = False
        for size, k, N in cands:
            if size <= best_n:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(N, k, d, D, rng, min(deadline, now + budget))
            if res is not None:
                consider(res[0], res[1])
                progress = True

        if not progress:
            window *= 2
        budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
