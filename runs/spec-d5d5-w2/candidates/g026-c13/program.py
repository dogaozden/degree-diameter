import math
import random
import time

import lib

MAX_GROUPS = 10      # groups tried per (N, attempt)
ITERS = 900          # annealing steps per (group, split) try
T_HOT = 2.0          # initial annealing temperature (unreached-pair units)
T_COLD = 0.2         # final annealing temperature
BUDGET_START = 0.5   # seconds per attempt at first
BUDGET_CAP = 6.0     # cap on seconds per attempt
WINDOW = 3           # new orders tried in [bestN+1, bestN+WINDOW]


# ----------------------------------------------------------------------------
# Baseline family: incidence graph of PG(2, q), used for D = 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW IDEA: two-orbit bi-Cayley lifts ("orbit-split bi-Cayley graphs").
#
# The parent uses one orbit pair (A_x, B_y) with a single connection set S of
# size d. Here each side has TWO orbits, A_0, A_1 and B_0, B_1, each of size N
# over a group G of order N. Connection sets S[i][j] (subsets of G) join
# A_i,x to B_j,x*g for g in S[i][j]. Sizes are
#     |S[0][0]| = a,  |S[0][1]| = d-a,  |S[1][0]| = d-a,  |S[1][1]| = a,
# with 1 <= a <= d-1, so every vertex has degree exactly d. The graph is
# bipartite (A side vs B side) with 4N vertices.
#
# Left multiplication by h in G is an automorphism that maps each orbit to
# itself, so the eccentricity of every vertex is determined by one source per
# orbit: A_0, A_1, B_0, B_1. Therefore 4 BFS runs decide the diameter.
# The search space is larger than the single-orbit case, so more orders
# and groups become reachable.
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


def _cost(N, T, invs, S, D):
    """Total unreached (source, vertex) pairs over the four orbit representatives."""
    tot = 4 * N
    # Forward moves from A_i: to B_j at offset (2+j)*N, via g in S[i][j].
    fwd = [[], []]
    for i in range(2):
        for j in range(2):
            off = (2 + j) * N
            for g in S[i][j]:
                fwd[i].append((off, g))
    # Backward moves from B_j: to A_i at offset i*N, via inverse of g in S[i][j].
    bwd = [[], []]
    for j in range(2):
        for i in range(2):
            off = i * N
            for g in S[i][j]:
                bwd[j].append((off, invs[g]))

    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(tot)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < 2 * N:
                    i = 0 if u < N else 1
                    row = T[u - i * N]
                    for off, g in fwd[i]:
                        v = off + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j = 0 if u < 3 * N else 1
                    row = T[u - (2 + j) * N]
                    for off, h in bwd[j]:
                        v = off + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += tot - count
    return total


def _anneal(N, T, invs, S, D, rng, iters, deadline):
    """Anneal the four connection sets (in place) to zero unreached pairs."""
    cur = _cost(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(2)
        j = rng.randrange(2)
        idx = rng.randrange(len(S[i][j]))
        c = rng.randrange(N)
        if c in S[i][j]:
            continue
        old = S[i][j][idx]
        S[i][j][idx] = c
        v = _cost(N, T, invs, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            S[i][j][idx] = old
    return S if cur == 0 else None


def _attempt(N, d, D, rng, deadline, tcache):
    """Try groups of order N with random orbit splits until diameter <= D is reached."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        key = (N, m, k, r)
        if key not in tcache:
            order, mul, inv = lib.semidirect_group(m, k, r)
            T = [[mul(x, g) for g in range(N)] for x in range(N)]
            invs = [inv(g) for g in range(N)]
            tcache[key] = (T, invs)
        T, invs = tcache[key]
        a = rng.randrange(1, d)  # split: sizes a, d-a on the diagonal / off-diagonal
        S = [[rng.sample(range(N), a), rng.sample(range(N), d - a)],
             [rng.sample(range(N), d - a), rng.sample(range(N), a)]]
        res = _anneal(N, T, invs, S, D, rng, ITERS, deadline)
        if res is not None:
            return T, res
    return None


def _edges_from(N, T, S):
    """Edges of the 4N-vertex orbit-split graph. Orbit o occupies ids o*N .. o*N+N-1."""
    edges = []
    for i in range(2):
        for j in range(2):
            for g in S[i][j]:
                for x in range(N):
                    edges.append((i * N + x, (2 + j) * N + T[x][g]))
    return edges


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

    # Record-matching case for D = 3: projective plane incidence graph.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 3 or D < 2:
        return best

    # Orbit-split search: 4N vertices, so N <= moore_bound / 4.
    Nmax = lib.moore_bound(d, D) // 4
    bestN = max(d, best_n // 4)
    budget = BUDGET_START
    tcache = {}

    while time.monotonic() < deadline:
        lo = bestN + 1
        if lo > Nmax:
            break
        N = min(Nmax, lo + rng.randrange(WINDOW))
        now = time.monotonic()
        att_deadline = min(deadline, now + budget)
        res = _attempt(N, d, D, rng, att_deadline, tcache)
        if res is not None:
            T, S = res
            consider(4 * N, _edges_from(N, T, S))
            if best_n == 4 * N:
                bestN = max(bestN, N)
            budget = BUDGET_START
        else:
            budget = min(BUDGET_CAP, budget * 1.3)
        # Keep the group-table cache small; drop entries for old orders.
        if len(tcache) > 200:
            tcache.clear()

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
