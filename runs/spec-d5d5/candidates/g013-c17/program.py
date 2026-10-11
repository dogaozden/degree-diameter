import itertools
import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# Parameters
# ----------------------------------------------------------------------------
MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per order N within one attempt (2-orbit search)
ITERS = 800                   # annealing steps per (group, connection set) try
TOP_SLACK = 8                 # search orders up to Nmax//2 + TOP_SLACK

ITERS4 = 350                  # annealing steps for the four-orbit search
GROUPS4 = 12                  # groups tried per order N in the four-orbit search
BUDGET4 = 2.0                 # seconds allotted to each order N
MAX_FAILS4 = 6                # stop after this many consecutive failed orders


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
# Group helpers shared by both searches.
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


# ----------------------------------------------------------------------------
# NEW: four-orbit bi-Cayley (two A-orbits, two B-orbits) over a group G.
#
# Vertices are orbit*N + g, orbit 0 = A0, 1 = A1, 2 = B0, 3 = B1, g in G.
# Connection sets S[i][j] (subsets of G) give edges (A_i, g) -- (B_j, g*s)
# for s in S[i][j]. Each A_i has degree |S[i][0]|+|S[i][1]|, each B_j has
# degree |S[0][j]|+|S[1][j]|. Using sizes [[a, d-a], [d-a, a]] keeps every
# degree at most d. Left multiplication by G is an automorphism, so only four
# BFS sources (one per orbit, at the identity) are needed. The order is 4N.
# ----------------------------------------------------------------------------

def _tables4(m, k, r):
    """Return (N, M, invs): multiplication table M[x][y] = x*y and inverses."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    N = order
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    invs = [inv(x) for x in range(N)]
    return N, M, invs


def _adj4(N, M, S):
    """Adjacency lists of the four-orbit lift for connection sets S."""
    adj = [[] for _ in range(4 * N)]
    for i in range(2):
        for j in range(2):
            for s in S[i][j]:
                for g in range(N):
                    a = i * N + g
                    b = (2 + j) * N + M[g][s]
                    adj[a].append(b)
                    adj[b].append(a)
    return adj


def _unreached4(N, adj, D):
    """Count (source, vertex) pairs at distance > D from the four orbit representatives."""
    V = 4 * N
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal4(N, M, sizes, D, rng, iters, deadline):
    """Simulated annealing over the four connection sets to zero unreached pairs."""
    S = [[rng.sample(range(N), sizes[i][j]) for j in range(2)] for i in range(2)]
    cur = _unreached4(N, _adj4(N, M, S), D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        i = rng.randrange(2)
        j = rng.randrange(2)
        if not S[i][j]:
            continue
        p = rng.randrange(len(S[i][j]))
        c = rng.randrange(N)
        if c in S[i][j]:
            continue
        old = S[i][j][p]
        S[i][j][p] = c
        v = _unreached4(N, _adj4(N, M, S), D)
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            S[i][j][p] = old
    return S if cur == 0 else None


def _attempt4(N, d, D, rng, deadline):
    """Try groups of order N for the four-orbit lift; return (N, M, S) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS4]:
        if time.monotonic() > deadline:
            return None
        Ng, M, _ = _tables4(m, k, r)
        a = rng.randint(1, d - 1)
        sizes = [[a, d - a], [d - a, a]]
        S = _anneal4(Ng, M, sizes, D, rng, ITERS4, deadline)
        if S is not None:
            return Ng, M, S
    return None


def _edges4(N, M, S):
    """Edge list of the four-orbit lift."""
    edges = []
    for i in range(2):
        for j in range(2):
            for s in S[i][j]:
                for g in range(N):
                    edges.append((i * N + g, (2 + j) * N + M[g][s]))
    return edges


def _search4(d, D, rng, deadline, consider, lo):
    """Ascend over orders N (graph has 4N vertices) until repeated failures or the deadline."""
    Nmax = lib._moore_bound(d, D) // 4
    N = max(lo, d + 1)
    fails = 0
    while N <= Nmax and time.monotonic() < deadline and fails < MAX_FAILS4:
        att_deadline = min(deadline, time.monotonic() + BUDGET4)
        res = _attempt4(N, d, D, rng, att_deadline)
        if res is None:
            fails += 1
        else:
            fails = 0
            Ng, M, S = res
            consider(4 * Ng, _edges4(Ng, M, S))
        N += 1


# ----------------------------------------------------------------------------
# Parent: bi-Cayley search over semidirect products (two vertex orbits).
# ----------------------------------------------------------------------------

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


def _search2(d, D, rng, deadline, consider):
    """Parent's two-orbit bi-Cayley search."""
    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    top = min(Nmax, Nmax // 2 + TOP_SLACK)
    cands = set(range(d + 1, top + 1))

    budget = 0.4
    while time.monotonic() < deadline and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
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
            budget *= 1.5


# ----------------------------------------------------------------------------
# Entry point
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
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    # Phase 1 (about 60% of the remaining time): four-orbit bi-Cayley search.
    now = time.monotonic()
    split = now + 0.6 * (deadline - now)
    lo = max(d + 1, best_n // 4)
    _search4(d, D, rng, split, consider, lo)

    # Phase 2: parent's two-orbit search with the remaining time.
    _search2(d, D, rng, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
