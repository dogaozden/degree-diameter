import math
import random
import time

import numpy as np

import lib

# ----------------------------------------------------------------------------
# Search parameters
# ----------------------------------------------------------------------------
MAX_GROUPS_PER_ATTEMPT = 10   # groups tried per (p, N) attempt
MAX_BASE_TRIES = 40           # random base-count matrices tried per group
ITERS = 800                   # annealing steps per (group, base, voltages) try
TOP_CANDIDATES = 30           # (p, N) pairs considered per scheduling pass
SAFETY = 0.75                 # fraction of time_limit we are allowed to use


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW IDEA: multi-orbit bi-Cayley voltage lifts with a base graph.
#
# Parent searched single-orbit bi-Cayley graphs (base = 1 vertex per side).
# Here the base is a p-by-p bipartite multigraph with count matrix C (row and
# column sums d). Vertices are A_i,x and B_j,y for orbit i,j in 0..p-1 and group
# elements x,y. Each cell (i,j) carries C[i][j] distinct voltages g, giving edges
# A_i,x -- B_j,x*g. Order is 2*p*N, so p = 2..5 reaches orders the single-orbit
# search cannot.
#
# Left multiplication by a group element is an automorphism, so the diameter is
# decided by BFS from the 2p orbit representatives only. The reach sets are kept
# as a dense 0/1 matrix and expanded with one matrix product per step, which is
# much faster than a Python BFS for these sizes.
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


def _base_connected(M, p):
    """True if the support of the p-by-p count matrix M connects all 2p base vertices."""
    seen = {0}
    stack = [0]
    while stack:
        u = stack.pop()
        if u < p:
            nbrs = [p + j for j in range(p) if M[u][j] > 0]
        else:
            j = u - p
            nbrs = [i for i in range(p) if M[i][j] > 0]
        for v in nbrs:
            if v not in seen:
                seen.add(v)
                stack.append(v)
    return len(seen) == 2 * p


def _base_counts(p, d, rng):
    """Random p-by-p nonnegative integer matrix with all row and column sums d, connected support."""
    if p == 1:
        return [[d]]
    for _ in range(MAX_BASE_TRIES):
        M = [[0] * p for _ in range(p)]
        for _ in range(d):
            perm = list(range(p))
            rng.shuffle(perm)
            for i in range(p):
                M[i][perm[i]] += 1
        if _base_connected(M, p):
            return M
    return None


def _unreached(p, N, Tm, S, D):
    """Total count of (source, vertex) pairs not within distance D, sources = orbit representatives."""
    V = 2 * p * N
    A = np.zeros((V, V), dtype=np.float32)
    xs = np.arange(N)
    for i in range(p):
        for j in range(p):
            for g in S[i][j]:
                a = i * N + xs
                b = p * N + j * N + Tm[:, g]
                A[a, b] = 1.0
                A[b, a] = 1.0
    src = [i * N for i in range(p)] + [p * N + j * N for j in range(p)]
    R = np.zeros((2 * p, V), dtype=np.float32)
    R[np.arange(2 * p), src] = 1.0
    for _ in range(D):
        R = ((R + R @ A) > 0).astype(np.float32)
    return int(2 * p * V - R.sum())


def _anneal(p, N, Tm, C, d, D, rng, iters, deadline):
    """Anneal the voltage sets S[i][j] (distinct elements per cell) to zero unreached pairs."""
    cells = [(i, j) for i in range(p) for j in range(p) if C[i][j] > 0]
    S = [[[] for _ in range(p)] for _ in range(p)]
    for i, j in cells:
        S[i][j] = rng.sample(range(N), C[i][j])
    cur = _unreached(p, N, Tm, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = max(0.2, 3.0 * (1.0 - it / iters))
        i, j = rng.choice(cells)
        t = rng.randrange(len(S[i][j]))
        g = rng.randrange(N)
        if g in S[i][j]:
            continue
        old = S[i][j][t]
        S[i][j][t] = g
        v = _unreached(p, N, Tm, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            S[i][j][t] = old
    return S if cur == 0 else None


def _attempt(p, N, d, D, rng, deadline):
    """Try groups of order N with a p-orbit base until a voltage assignment has diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        Tm = np.array([[mul(x, g) for g in range(N)] for x in range(N)], dtype=np.int64)
        C = _base_counts(p, d, rng)
        if C is None:
            continue
        S = _anneal(p, N, Tm, C, d, D, rng, ITERS, deadline)
        if S is not None:
            return Tm, S, C
    return None


def _edges(p, N, Tm, S):
    """Edge list of the lift: A_i,x -- B_j, Tm[x, g] for each voltage g in S[i][j]."""
    out = []
    for i in range(p):
        for j in range(p):
            for g in S[i][j]:
                for x in range(N):
                    out.append((i * N + x, p * N + j * N + int(Tm[x, g])))
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + SAFETY * time_limit
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

    Mb = lib._moore_bound(d, D)
    cands = []
    for p in range(1, 6):
        for N in range(d + 1, Mb // (2 * p) + 1):
            order = 2 * p * N
            if order > Mb:
                break
            cands.append((order, p, N))
    cands.sort()

    budget = 1.0
    while time.monotonic() < deadline:
        pool = [c for c in cands if c[0] > best_n][:TOP_CANDIDATES]
        if not pool:
            break
        success = False
        for order, p, N in pool:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(p, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            Tm, S, C = res
            consider(2 * p * N, _edges(p, N, Tm, S))
            if best_n < 2 * p * N:
                # Result failed validation; drop this candidate so it is not retried forever.
                cands.remove((order, p, N))
            success = True
            break
        if not success:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
