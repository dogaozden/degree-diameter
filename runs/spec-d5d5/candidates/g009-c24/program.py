import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per order N within one attempt
ITERS = 600                   # annealing steps per (group, connection set) try
T_HOT = 1.5                   # initial annealing temperature (bi-Cayley)
T_COLD = 0.15                 # final annealing temperature (bi-Cayley)
ITERS2 = 1500                 # annealing steps per group for the two-orbit search
T2_HOT = 3.0                  # two-orbit objective sums over 4 sources, so scale up
T2_COLD = 0.3
TWO_ORBIT_WINDOW = 6          # orders N tried above the current record / 4


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
# Groups: semidirect products Z_m x|_r Z_k of order N (identity is code 0).
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
# Search 1: bi-Cayley graphs (one orbit per side). Vertices A_x, B_y, x,y in G,
# edge A_x -- B_{x s} for s in S, |S| = d.
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
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    if cur == 0:
        return S
    return None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a connection set with diameter <= D."""
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


def _search_bicayley(d, D, rng, deadline, consider):
    """Bi-Cayley search over orders N, descending, with doubling budgets."""
    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    top = min(Nmax, Nmax // 2 + 6)
    cands = set(range(d + 1, top + 1))
    budget = 0.4
    while time.monotonic() < deadline and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(N, d, D, rng, min(deadline, now + budget))
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


# ----------------------------------------------------------------------------
# Search 2 (new): two-orbit group voltage lifts.
#
# Base graph: A_0, A_1 | B_0, B_1, with dart multiplicities
#     c = [[a, d-a], [d-a, a]]
# which is forced by regularity (row sums = column sums = d) once each block
# is taken to be a single list of distinct voltages.  Vertices are
#     A_i,x  -> index i*N + x
#     B_j,y  -> index 2N + j*N + y
# with an edge A_i,x -- B_j,T[x][s] for every voltage s in V[i][j].
# Left multiplication by G is an automorphism, so BFS from the four orbit
# representatives A_0,e, A_1,e, B_0,e, B_1,e decides the diameter.
# This gives 4N vertices, so the record 336 is beaten at N >= 85.
# ----------------------------------------------------------------------------

def _adj2(N, V, T):
    """Adjacency lists of the two-orbit lift."""
    adj = [[] for _ in range(4 * N)]
    for i in (0, 1):
        for j in (0, 1):
            base_b = 2 * N + j * N
            for s in V[i][j]:
                for x in range(N):
                    a = i * N + x
                    b = base_b + T[x][s]
                    adj[a].append(b)
                    adj[b].append(a)
    return adj


def _unreached2(N, V, T, D):
    """Count (orbit representative, vertex) pairs not within distance D."""
    adj = _adj2(N, V, T)
    M = 4 * N
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(M)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += M - count
    return total


def _edges2(N, V, T):
    """Edge list of the two-orbit lift."""
    edges = []
    for i in (0, 1):
        for j in (0, 1):
            for s in V[i][j]:
                for x in range(N):
                    edges.append((i * N + x, 2 * N + j * N + T[x][s]))
    return edges


def _anneal2(N, T, a, d, D, rng, iters, deadline):
    """Anneal the four voltage blocks (each block has distinct voltages)."""
    c = [[a, d - a], [d - a, a]]
    V = [[rng.sample(range(N), c[i][j]) for j in (0, 1)] for i in (0, 1)]
    cur = _unreached2(N, V, T, D)
    blocks = [(i, j) for i in (0, 1) for j in (0, 1)]
    for it in range(iters):
        if cur == 0:
            return V
        if time.monotonic() > deadline:
            break
        temp = T2_HOT * (T2_COLD / T2_HOT) ** (it / iters)
        i, j = rng.choice(blocks)
        k = rng.randrange(c[i][j])
        g = rng.randrange(N)
        if g in V[i][j]:
            continue
        V2 = [[list(V[p][q]) for q in (0, 1)] for p in (0, 1)]
        V2[i][j][k] = g
        v = _unreached2(N, V2, T, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            V, cur = V2, v
    return V if cur == 0 else None


def _attempt2(N, d, D, rng, deadline):
    """Try groups of order N with a random dart split a in 1..d-1."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        a = rng.randint(1, d - 1)
        V = _anneal2(N, T, a, d, D, rng, ITERS2, deadline)
        if V is not None:
            return T, V
    return None


def _search_two_orbit(d, D, rng, deadline, consider, best_n):
    """Search two-orbit lifts for orders N with 4N above the current record."""
    lo = best_n // 4 + 1
    hi = min(lib._moore_bound(d, D) // 4, lo + TWO_ORBIT_WINDOW)
    if d < 2 or hi < lo:
        return
    cands = set(range(lo, hi + 1))
    budget = 3.0
    while time.monotonic() < deadline and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt2(N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, V = res
            consider(4 * N, _edges2(N, V, T))
            cands = {M for M in cands if M > N}
            if N + 1 <= hi:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total_deadline = start + 0.88 * time_limit
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

    if D >= 2 and d >= 1:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < total_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    # Stage 1: bi-Cayley search (establishes the baseline).
    stage1_deadline = min(total_deadline, start + 0.45 * time_limit)
    _search_bicayley(d, D, rng, stage1_deadline, consider)

    # Stage 2: two-orbit voltage lifts, aimed above the current record.
    _search_two_orbit(d, D, rng, total_deadline, consider, best_n)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
