import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per (order, orbit count) within one attempt
ITERS = 400                   # annealing steps per bi-Cayley (group, connection set) try
MULTI_ITERS = 1500            # annealing steps per multi-orbit try
MULTI_KS = (2, 3, 4, 6)       # numbers of vertex orbits per side tried in the multi-orbit phase


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Single-orbit bi-Cayley search over semidirect products Z_m x| Z_k of order N.
#
# Vertices A_x and B_y (x, y in G). Edge A_x -- B_{x s} for s in S, |S| = d.
# Left multiplication is an automorphism, so eccentricities from A_0 and B_0
# decide the diameter.
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


def _unreached(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a connection set with diameter <= D, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# NEW: multi-orbit bi-Cayley graphs ("k-orbit voltage lifts").
#
# Take k orbits A_0..A_{k-1} and k orbits B_0..B_{k-1}, each a copy of a group G
# of order N. For every orbit pair (i, j) choose a set S_ij of c_ij group elements,
# where the count matrix C = (c_ij) has all row sums and column sums equal to d.
# Edges: A_{i,x} -- B_{j, x s} for s in S_ij.
#
# Left multiplication by G permutes each orbit, so the graph is bipartite,
# regular of degree d, and its diameter is determined by BFS from the 2k
# orbit representatives A_{i,e} and B_{j,e}. A single-orbit bi-Cayley graph is
# the k = 1 case. Larger k lets a graph of order 2kN reach the orders that
# cyclic/semidirect single-orbit searches miss, e.g. 2*2*85 = 340 > 336.
# ----------------------------------------------------------------------------

def _count_matrix(k, d, rng):
    """Random k x k count matrix with all row and column sums d: sum of d random permutation matrices."""
    C = [[0] * k for _ in range(k)]
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            C[i][p[i]] += 1
    return C


def _multi_cost(k, N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D over the 2k orbit representatives."""
    KN = k * N
    M = 2 * KN
    flatA = [[(j, s) for j in range(k) for s in S[i][j]] for i in range(k)]
    flatB = [[(i, invs[s]) for i in range(k) for s in S[i][j]] for j in range(k)]
    total = 0
    for src in range(0, M, N):          # A_{i,0} at i*N, B_{j,0} at KN + j*N
        seen = bytearray(M)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            if not frontier:
                break
            nxt = []
            for u in frontier:
                if u < KN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, s in flatA[i]:
                        v = KN + j * N + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - KN, N)
                    row = T[y]
                    for i, si in flatB[j]:
                        v = i * N + row[si]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
        total += M - count
    return total


def _multi_anneal(k, N, T, invs, C, D, rng, iters, deadline):
    """Anneal the connection sets S_ij (fixed sizes c_ij) to zero unreached pairs."""
    cells = [(i, j) for i in range(k) for j in range(k) if C[i][j]]
    S = [[[] for _ in range(k)] for _ in range(k)]
    for i, j in cells:
        S[i][j] = rng.sample(range(N), C[i][j])
    cur = _multi_cost(k, N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        i, j = rng.choice(cells)
        p = rng.randrange(len(S[i][j]))
        g = rng.randrange(N)
        if g in S[i][j]:
            continue
        old = S[i][j][p]
        S[i][j][p] = g
        v = _multi_cost(k, N, T, invs, S, D)
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            S[i][j][p] = old
    return S if cur == 0 else None


def _multi_attempt(k, N, d, D, rng, deadline):
    """Try groups of order N with a random count matrix until a k-orbit graph has diameter <= D."""
    if N < d:
        return None
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        C = _count_matrix(k, d, rng)
        S = _multi_anneal(k, N, T, invs, C, D, rng, MULTI_ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _multi_edges(k, N, T, S):
    """Edge list and order of the k-orbit bi-Cayley graph."""
    KN = k * N
    edges = []
    for i in range(k):
        for j in range(k):
            for s in S[i][j]:
                for x in range(N):
                    edges.append((i * N + x, KN + j * N + T[x][s]))
    return 2 * KN, edges


def _multi_phase(d, D, rng, deadline, best_fn, consider):
    """Round-robin over orbit counts k, always targeting orders above the current best."""
    moore = lib._moore_bound(d, D)
    Ns = {k: 0 for k in MULTI_KS}
    budget = {k: 3.0 for k in MULTI_KS}
    active = True
    while active and time.monotonic() < deadline:
        active = False
        for k in MULTI_KS:
            if time.monotonic() >= deadline:
                break
            N = max(Ns[k], best_fn() // (2 * k) + 1, d)
            Ns[k] = N
            if 2 * k * N > moore:
                continue
            active = True
            att = min(deadline, time.monotonic() + budget[k])
            res = _multi_attempt(k, N, d, D, rng, att)
            if res is None:
                budget[k] = min(budget[k] * 1.5, 30.0)
                continue
            T, S = res
            n, edges = _multi_edges(k, N, T, S)
            consider(n, edges)
            Ns[k] = N + 1
            budget[k] = 3.0


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.85 * time_limit
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0] = n
            best[1] = e

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best[0], best[1]

    # Phase 1: single-orbit bi-Cayley search (k = 1).
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + 3)
    cands = set(range(d + 1, top + 1))
    p1 = start + 0.3 * total
    budget = 0.4
    while time.monotonic() < p1 and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= p1:
                break
            att_deadline = min(p1, now + budget)
            res = _attempt(N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 2

    # Phase 2: multi-orbit bi-Cayley search, aimed above the current best order.
    _multi_phase(d, D, rng, deadline, lambda: best[0], consider)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
