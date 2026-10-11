import math
import random
import time

import lib

ITERS = 500        # annealing steps per group try
MAX_GROUPS = 8     # groups tried per attempt


# ----------------------------------------------------------------------------
# Baseline families (cheap, validated before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: 2-vertex-per-side bi-Cayley lifts over semidirect products.
#
# Base multigraph on A_0, A_1, B_0, B_1 with darts (i, j, g):
#   A_{i,x} -- B_{j, x*g}   for every g in S[i][j].
# Out-degree of A_i and in-degree of B_j are both d, so the lift is d-regular,
# bipartite, and has 4N vertices. Left multiplication is an automorphism, so
# eccentricities from the four sources A_{i,e}, B_{j,e} decide the diameter.
# Group elements in each S[i][j] are distinct, so the graph is simple.
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


def _adjacency(b, N, S, invs):
    """Implicit adjacency: outs[i] lists (j, g) and ins[j] lists (i, g^-1)."""
    outs = [[(j, g) for j in range(b) for g in S[i][j]] for i in range(b)]
    ins = [[(i, invs[g]) for i in range(b) for g in S[i][j]] for j in range(b)]
    return outs, ins


def _cost(b, N, T, outs, ins, D):
    """Number of (source, vertex) pairs not within distance D, over one source per orbit."""
    bN = b * N
    V = 2 * bN
    total = 0
    sources = [i * N for i in range(b)] + [bN + j * N for j in range(b)]
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < bN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in outs[i]:
                        v = bN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - bN, N)
                    row = T[y]
                    for i, h in ins[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(b, N, T, invs, sz, D, rng, iters, deadline):
    """Anneal the connection sets S[i][j] (sizes sz[i][j]) to zero unreached pairs."""
    S = [[rng.sample(range(N), sz[i][j]) for j in range(b)] for i in range(b)]
    outs, ins = _adjacency(b, N, S, invs)
    cur = _cost(b, N, T, outs, ins, D)
    cells = [(i, j) for i in range(b) for j in range(b) if sz[i][j] > 0]
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = max(0.3, 3.0 * (1.0 - it / iters))
        i, j = rng.choice(cells)
        p = rng.randrange(sz[i][j])
        c = rng.randrange(N)
        if c in S[i][j]:
            continue
        old = S[i][j][p]
        S[i][j][p] = c
        outs2, ins2 = _adjacency(b, N, S, invs)
        v = _cost(b, N, T, outs2, ins2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
            outs, ins = outs2, ins2
        else:
            S[i][j][p] = old
    return S if cur == 0 else None


def _attempt(b, N, d, D, rng, deadline):
    """Try groups of order N (base size b) until a valid connection family is found."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        if b == 1:
            sz = [[d]]
        else:
            a = rng.randint(1, d - 1)          # a = 0 or d would be disconnected
            sz = [[a, d - a], [d - a, a]]
        S = _anneal(b, N, T, invs, sz, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Calibration case: incidence graph of PG(2, d-1) meets the bound.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    consider(*lib.haar_graph(d, range(d)))
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    # Phase 1 (safety net): single-orbit bi-Cayley lift, 2N vertices, descending N.
    Nmax1 = lib._moore_bound(d, D) // 2
    ph1_end = start + 0.3 * (deadline - start)
    step = max(1, Nmax1 // 40)
    for N in range(Nmax1, d, -step):
        if time.monotonic() >= ph1_end:
            break
        att = min(ph1_end, time.monotonic() + 0.25)
        res = _attempt(1, N, d, D, rng, att)
        if res is not None:
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S[0][0]]
            consider(2 * N, edges)
            break

    # Phase 2 (main search): two-orbit-per-side lifts, 4N vertices.
    # Only orders with 4N > current best are useful, so start just above it.
    Nmax2 = lib._moore_bound(d, D) // 4
    N = max(d + 1, best[0] // 4 + 1)
    while N <= Nmax2 and time.monotonic() < deadline:
        att = min(deadline, time.monotonic() + 1.2)
        res = _attempt(2, N, d, D, rng, att)
        if res is not None:
            T, S = res
            edges = []
            for i in range(2):
                for j in range(2):
                    for g in S[i][j]:
                        for x in range(N):
                            edges.append((i * N + x, 2 * N + j * N + T[x][g]))
            consider(4 * N, edges)
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
