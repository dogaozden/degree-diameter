import math
import random
import time

import lib

ITERS = 500                  # annealing steps per (group, base structure) try
T_HOT = 2.0                  # initial temperature (in unreached-pair units)
T_COLD = 0.2                 # final temperature
MAX_GROUPS = 8               # groups tried per (p, N) attempt
P_CHOICES = (1, 2, 3, 4)     # number of A-vertices (= B-vertices) in the base multigraph
MAX_ORDER = 800              # cap on group order (keeps multiplication tables small)


# ----------------------------------------------------------------------------
# Safe baseline families. Each result is checked by lib.is_valid before use.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect products Z_m x| Z_k.
#
# Base multigraph: p A-vertices A_0..A_{p-1} and p B-vertices B_0..B_{p-1}.
# It is d-regular: d random perfect matchings between A and B, each matching
# contributes one dart per A-vertex. Each dart (i, j, g) carries a voltage g
# in the group G of order N. The lift has vertices (b, x), b a base vertex,
# x in G, and edges (A_i, x) -- (B_j, x*g), so it has 2*p*N vertices.
#
# Left multiplication by G is an automorphism of the lift, so the diameter
# condition only needs BFS from (b, identity) for every base vertex b.
# Parallel darts between the same (i, j) carry distinct voltages, so the
# lift has no duplicate edges.
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


def _init_darts(p, d, N, rng):
    """Random d-regular base multigraph with voltages; parallel darts get distinct voltages."""
    darts = []
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        for i in range(p):
            j = perm[i]
            used = {g for a, b, g in darts if a == i and b == j}
            while True:
                g = rng.randrange(N)
                if g not in used:
                    break
            darts.append((i, j, g))
    return darts


def _tables(p, darts, invs):
    """Per-base-vertex dart lists used by the BFS."""
    dA = [[] for _ in range(p)]
    dB = [[] for _ in range(p)]
    for i, j, g in darts:
        dA[i].append((j, g))
        dB[j].append((i, invs[g]))
    return dA, dB


def _unreached(p, N, T, dA, dB, D):
    """Total count of (source, vertex) pairs at distance > D, summed over the 2p base sources."""
    V = 2 * p * N
    total = 0
    for src in range(2 * p):
        seen = bytearray(V)
        s = src * N
        seen[s] = 1
        count = 1
        frontier = [s]
        for _ in range(D):
            nxt = []
            for u in frontier:
                b, x = divmod(u, N)
                row = T[x]
                if b < p:
                    for j, g in dA[b]:
                        v = (p + j) * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    for i, h in dB[b - p]:
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


def _anneal(p, N, T, invs, d, D, rng, deadline):
    """Simulated annealing over the voltages of a random base structure."""
    darts = _init_darts(p, d, N, rng)
    dA, dB = _tables(p, darts, invs)
    cur = _unreached(p, N, T, dA, dB, D)
    if cur == 0:
        return darts
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        k = rng.randrange(len(darts))
        i, j, g = darts[k]
        g2 = rng.randrange(N)
        if g2 == g:
            continue
        if any(a == i and b == j and c == g2 for a, b, c in darts):
            continue
        darts[k] = (i, j, g2)
        dA2, dB2 = _tables(p, darts, invs)
        v = _unreached(p, N, T, dA2, dB2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[k] = (i, j, g)
    if cur == 0:
        return darts
    return None


def _attempt(p, N, d, D, rng, deadline):
    """Try groups of order N with a p-vertex base until one lift has diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        darts = _anneal(p, N, T, invs, d, D, rng, deadline)
        if darts is not None:
            return T, darts, p, N
    return None


def _lift_edges(p, N, T, darts):
    """Expand the base multigraph with voltages into the full lift: (order, edges)."""
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, (p + j) * N + T[x][g]))
    return 2 * p * N, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
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

    # Safe baselines.
    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    # Candidate (V, p, N) lifts with V = 2*p*N strictly above the current best.
    Vmax = lib._moore_bound(d, D)
    base_cands = set()
    for p in P_CHOICES:
        N0 = max(d, (best_n + 1 + 2 * p - 1) // (2 * p))
        for off in list(range(0, 12)) + [20, 40, 80, 160]:
            N = N0 + off
            V = 2 * p * N
            if V <= Vmax and N <= MAX_ORDER and V > best_n:
                base_cands.add((V, p, N))
    base_cands = sorted(base_cands)

    budget = 0.25
    while time.monotonic() < deadline:
        todo = [c for c in base_cands if c[0] > best_n]
        if not todo:
            break
        progress = False
        for V, p, N in todo:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(p, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, darts, pp, NN = res
            n, e = _lift_edges(pp, NN, T, darts)
            consider(n, e)
            progress = True
            break
        if not progress:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
