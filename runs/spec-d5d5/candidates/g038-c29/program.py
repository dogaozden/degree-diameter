import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per order N within one single-orbit attempt
ITERS = 800                   # annealing steps per single-orbit try
TOP_SLACK = 8                 # single-orbit search orders up to Nmax//2 + TOP_SLACK
SINGLE_PHASE_FRAC = 0.3       # share of time for the single-orbit search

# Two-orbit bi-Cayley search (new in this version).
K_ORBITS = 2                  # orbits per side; graph order is 2*K*N
MULTI_GROUPS = 25             # groups tried per attempt in the multi-orbit search
MULTI_ITERS = 400             # annealing steps per (group, block-size) try
MULTI_WINDOW = 4              # orders tried per round before the budget grows


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
# Shared group helpers.
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
# Single-orbit bi-Cayley search (baseline from the parent).
# Vertices A_x and B_y (x, y in G). Edge A_x -- B_{x s} for s in S, |S| = d.
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


# ----------------------------------------------------------------------------
# NEW: two-orbit bi-Cayley search.
#
# Vertices A_{i,x} and B_{j,y} for orbit indices i, j in {0..K-1} and x, y in G.
# Edge A_{i,x} -- B_{j, x g} for g in S[i][j]. Left multiplication by G is an
# automorphism, so the diameter can be checked from one source per orbit.
# Degrees: A-side sum_j |S[i][j]|, B-side sum_i |S[i][j]|. With the block-size
# matrix sz = [[p, d-p], [d-p, p]] both sums equal d, so the graph is d-regular.
# Order 2*K*N, so beating 336 with K = 2 needs N >= 85.
# ----------------------------------------------------------------------------

def _multi_adj(N, K, T, S):
    """Adjacency lists of the K-orbit bi-Cayley graph described by connection blocks S."""
    V = 2 * K * N
    adj = [[] for _ in range(V)]
    for i in range(K):
        for j in range(K):
            base_b = K * N + j * N
            for g in S[i][j]:
                for x in range(N):
                    a = i * N + x
                    b = base_b + T[x][g]
                    adj[a].append(b)
                    adj[b].append(a)
    return adj


def _unreached_multi(N, K, adj, D):
    """Count (source, vertex) pairs not within distance D, for one source per orbit."""
    V = 2 * K * N
    total = 0
    for src in range(0, V, N):  # A_0, A_1, ..., B_0, ... one representative per orbit
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


def _anneal_multi(N, K, T, sz, d, D, rng, iters, deadline):
    """Anneal the connection blocks of a K-orbit bi-Cayley graph to zero unreached pairs."""
    S = [[rng.sample(range(N), sz[i][j]) for j in range(K)] for i in range(K)]
    adj = _multi_adj(N, K, T, S)
    cur = _unreached_multi(N, K, adj, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(K)
        j = rng.randrange(K)
        if sz[i][j] == 0:
            continue
        block = S[i][j]
        pos = rng.randrange(sz[i][j])
        c = rng.randrange(N)
        if c in block:
            continue
        old = block[pos]
        block[pos] = c
        adj2 = _multi_adj(N, K, T, S)
        v = _unreached_multi(N, K, adj2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            block[pos] = old
    return S if cur == 0 else None


def _attempt_multi(N, d, D, rng, deadline):
    """Try groups of order N with a random block split until a valid K-orbit graph appears."""
    groups = _groups(N)
    if not groups:
        return None
    rng.shuffle(groups)
    K = K_ORBITS
    for m, k, r in groups[:MULTI_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        p = rng.randrange(1, d)
        sz = [[p, d - p], [d - p, p]]
        S = _anneal_multi(N, K, T, sz, d, D, rng, MULTI_ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _multi_edges(N, K, T, S):
    """Edge list (A index, B index) for a K-orbit bi-Cayley graph, all distinct by construction."""
    edges = []
    for i in range(K):
        for j in range(K):
            for g in S[i][j]:
                for x in range(N):
                    edges.append((i * N + x, K * N + j * N + T[x][g]))
    return edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    moore = lib._moore_bound(d, D)

    # ---- Phase 1: single-orbit bi-Cayley search (parent method), bounded share of time.
    single_deadline = min(deadline, start + SINGLE_PHASE_FRAC * time_limit)
    Nmax = moore // 2
    top = min(Nmax, Nmax // 2 + TOP_SLACK)
    cands = set(range(d + 1, top + 1))
    budget = 0.4
    while time.monotonic() < single_deadline and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= single_deadline:
                break
            att_deadline = min(single_deadline, now + budget)
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

    # ---- Phase 2: two-orbit bi-Cayley search, climbing past the current best order.
    Nmax_multi = moore // (2 * K_ORBITS)
    lo = best_n // (2 * K_ORBITS) + 1
    lo = max(lo, d + 1)
    budget = 1.0
    while time.monotonic() < deadline and lo <= Nmax_multi:
        found = False
        for N in range(lo, min(Nmax_multi, lo + MULTI_WINDOW) + 1):
            if time.monotonic() >= deadline:
                break
            att_deadline = min(deadline, time.monotonic() + budget)
            res = _attempt_multi(N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, S = res
            consider(2 * K_ORBITS * N, _multi_edges(N, K_ORBITS, T, S))
            lo = N + 1
            found = True
            break
        if not found:
            budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
