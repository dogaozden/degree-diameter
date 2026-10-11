import math
import random
import time

import lib

ITERS = 1500          # annealing steps per (group, voltage) attempt
T_HOT = 1.2           # initial annealing temperature (unreached-pair units)
T_COLD = 0.1          # final annealing temperature
MAX_GROUPS = 8        # groups tried per attempt
ATTEMPT_SECONDS = 4.0 # wall-clock budget per attempt
WINDOW = 20           # how far above the current lower bound to sample orders
PS = (1, 2, 3, 4)     # base-graph sizes per side (number of base vertices per side)


# ----------------------------------------------------------------------------
# Fallback families (always checked with lib.is_valid before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Voltage lifts of small bipartite base multigraphs over finite groups.
#
# Base: p vertices A_0..A_{p-1} and p vertices B_0..B_{p-1}. Layer k (0 <= k < d)
# is a permutation perm[k] of range(p), giving darts A_i -> B_{perm[k][i]} with
# voltage volt[k][i] in G. The base is d-regular, so the lift is d-regular.
#
# Lift vertices: A_i,x -> index i*N + x; B_j,y -> index p*N + j*N + y.
# Edge: A_i,x -- B_j,(x*g) for each dart (i, j, g).
# Left multiplication by G is an automorphism, so eccentricities need only
# be checked from the identity vertex of each base vertex.
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


def _adjacency(p, d, perm, volt, invs):
    """Per base vertex: darts out of each A_i and into each B_j (with inverted voltage)."""
    adjA = [[] for _ in range(p)]
    adjB = [[] for _ in range(p)]
    for k in range(d):
        pk = perm[k]
        vk = volt[k]
        for i in range(p):
            j = pk[i]
            g = vk[i]
            adjA[i].append((j, g))
            adjB[j].append((i, invs[g]))
    return adjA, adjB


def _cost(p, N, D, T, adjA, adjB):
    """Number of (source, vertex) pairs left unreached within distance D.

    Sources are the identity vertex of each base vertex (A_i,0 and B_j,0).
    """
    V = 2 * p * N
    base = p * N
    total = 0
    for src in range(2 * p):
        seen = bytearray(V)
        s = src * N if src < p else base + (src - p) * N
        seen[s] = 1
        count = 1
        frontier = [s]
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
                    for i, gi in adjB[j]:
                        v = i * N + row[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            if not nxt:
                break
            frontier = nxt
        total += V - count
    return total


def _anneal(p, N, D, d, T, invs, perm, rng, deadline):
    """Simulated annealing over voltages to drive the unreached-pair count to zero."""
    volt = [[rng.randrange(N) for _ in range(p)] for _ in range(d)]

    def cost():
        adjA, adjB = _adjacency(p, d, perm, volt, invs)
        return _cost(p, N, D, T, adjA, adjB)

    cur = cost()
    for it in range(ITERS):
        if cur == 0:
            return volt
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        k = rng.randrange(d)
        i = rng.randrange(p)
        c = rng.randrange(N)
        old = volt[k][i]
        if c == old:
            continue
        volt[k][i] = c
        v = cost()
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            volt[k][i] = old
    return volt if cur == 0 else None


def _attempt(p, N, d, D, rng, deadline):
    """Try groups of order N with a random base structure until one lift has diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    perm = [rng.sample(range(p), p) for _ in range(d)]
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        volt = _anneal(p, N, D, d, T, invs, perm, rng, deadline)
        if volt is not None:
            return T, perm, volt
    return None


def _lift_edges(p, N, d, T, perm, volt):
    """Materialize the lift as (n, edges) with duplicates removed."""
    base = p * N
    edges = set()
    for k in range(d):
        for i in range(p):
            j = perm[k][i]
            g = volt[k][i]
            for x in range(N):
                edges.add((i * N + x, base + j * N + T[x][g]))
    return 2 * base, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget_end = start + max(1.0, min(0.75 * time_limit, time_limit - 8.0))
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

    # Moore-optimal case: incidence graph of PG(2, d-1).
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

    try:
        while time.monotonic() < budget_end:
            options = []
            for p in PS:
                nmax = moore // (2 * p)          # total vertices 2*p*N <= moore
                lo = best_n // (2 * p) + 1       # must strictly beat the current best
                if lo <= nmax:
                    options.append((p, lo, min(nmax, lo + WINDOW)))
            if not options:
                break
            p, lo, hi = rng.choice(options)
            N = rng.randint(lo, hi)
            now = time.monotonic()
            res = _attempt(p, N, d, D, rng, min(budget_end, now + ATTEMPT_SECONDS))
            if res is not None:
                T, perm, volt = res
                n, e = _lift_edges(p, N, d, T, perm, volt)
                consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
