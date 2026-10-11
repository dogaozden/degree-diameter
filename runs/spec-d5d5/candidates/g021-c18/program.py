import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per order N within one k=1 attempt
ITERS = 600                   # annealing steps per (group, connection set) try, k=1
MAX_GROUPS2 = 8               # groups tried per (N, dart matrix), k=2
ITERS2 = 800                  # annealing steps per (group, dart matrix), k=2
K2_BUDGET = 3.0               # seconds spent on each order N in the k=2 phase
T_HOT = 1.5                   # initial annealing temperature (in unreached-pair units)
T_COLD = 0.15                 # final annealing temperature


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
# Shared group enumeration.
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
# k = 1: bi-Cayley graphs over a group G of order N (parent construction).
# A_x -- B_{x s} for s in S, |S| = d.
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


def _search_k1(d, D, rng, deadline, consider, min_n):
    """Parent's one-orbit bi-Cayley search, restricted to orders giving more than min_n vertices."""
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + 6)
    cands = {N for N in range(d + 1, top + 1) if 2 * N > min_n}
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
            consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 2


# ----------------------------------------------------------------------------
# k = 2 (new): two-orbit voltage lifts over a group G of order N.
#
# Base graph: A_0, A_1 on one side, B_0, B_1 on the other. Dart matrix
# M = [[a, d-a], [d-a, a]] gives a darts A_i -- B_j, each with a voltage g in G.
# The lift has vertices (block, x), x in G, and joins (A_i, x) to (B_j, x*g).
# Left multiplication by h in G is an automorphism, so each block is one
# orbit. Eccentricities only need one source per block: (A_0, e), (A_1, e),
# (B_0, e), (B_1, e). The lift has 4N vertices and is bipartite by construction.
# Only connected dart matrices (1 <= a <= d/2) are used.
# ----------------------------------------------------------------------------

def _adj2(k, darts, invs):
    """Adjacency of the base darts: Aadj[i] lists (j, g), Badj[j] lists (i, g^-1)."""
    Aadj = [[] for _ in range(k)]
    Badj = [[] for _ in range(k)]
    for i in range(k):
        for j in range(k):
            for g in darts[i][j]:
                Aadj[i].append((j, g))
                Badj[j].append((i, invs[g]))
    return Aadj, Badj


def _cost2(N, k, T, Aadj, Badj, D):
    """Total unreached pairs over the 2k block-representative sources, for radius D."""
    V = 2 * k * N
    total = 0
    for side in range(2):
        for b in range(k):
            src = (side * k + b) * N
            seen = bytearray(V)
            seen[src] = 1
            frontier = [src]
            cnt = 1
            for _ in range(D):
                nxt = []
                for u in frontier:
                    blk, x = divmod(u, N)
                    row = T[x]
                    if blk < k:
                        for j, g in Aadj[blk]:
                            v = (k + j) * N + row[g]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                    else:
                        for i, h in Badj[blk - k]:
                            v = i * N + row[h]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                cnt += len(nxt)
                frontier = nxt
                if not frontier:
                    break
            total += V - cnt
    return total


def _anneal2(N, k, T, invs, M, d, D, rng, iters, deadline):
    """Anneal the voltages of the darts so that the lift has diameter <= D.

    The dart (0, 0, 0) is fixed to the identity: relabelling the B_0 block
    by a group element normalises it at no cost to the search space.
    Distinct darts between the same base pair get distinct voltages, so
    the lift has no duplicate edges and every vertex has degree exactly d.
    """
    darts = [[[] for _ in range(k)] for _ in range(k)]
    movable = []
    for i in range(k):
        for j in range(k):
            cnt = M[i][j]
            if cnt == 0:
                continue
            if i == 0 and j == 0:
                darts[0][0] = [0] + rng.sample(range(1, N), cnt - 1)
                for s in range(1, cnt):
                    movable.append((0, 0, s))
            else:
                darts[i][j] = rng.sample(range(N), cnt)
                for s in range(cnt):
                    movable.append((i, j, s))
    Aadj, Badj = _adj2(k, darts, invs)
    cur = _cost2(N, k, T, Aadj, Badj, D)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i, j, s = movable[rng.randrange(len(movable))]
        lst = darts[i][j]
        g = rng.randrange(N)
        if g in lst:
            continue
        old = lst[s]
        lst[s] = g
        Aadj, Badj = _adj2(k, darts, invs)
        v = _cost2(N, k, T, Aadj, Badj, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            lst[s] = old
    if cur == 0:
        return darts
    return None


def _attempt2(N, k, d, D, M, rng, deadline):
    """Try groups of order N with dart matrix M until one yields diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS2]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        darts = _anneal2(N, k, T, invs, M, d, D, rng, ITERS2, deadline)
        if darts is not None:
            return T, darts
    return None


def _edges2(N, k, T, darts):
    """Expand the base darts into the full lift edge list (no duplicates by construction)."""
    E = []
    for i in range(k):
        for j in range(k):
            for g in darts[i][j]:
                for x in range(N):
                    E.append((i * N + x, (k + j) * N + T[x][g]))
    return E


def _search_k2(d, D, rng, deadline, consider, min_n):
    """Search two-orbit lifts for orders N with 4N > min_n, ascending from the smallest candidate."""
    k = 2
    Mats = [[[a, d - a], [d - a, a]] for a in range(1, d // 2 + 1)]
    if not Mats:
        return
    Nmax = lib._moore_bound(d, D) // (2 * k)
    N = max(d + 1, min_n // (2 * k) + 1)
    while N <= Nmax and time.monotonic() < deadline:
        per = K2_BUDGET / len(Mats)
        for M in Mats:
            if time.monotonic() >= deadline:
                break
            if M[0][0] > N or M[0][1] > N:
                continue
            att = min(deadline, time.monotonic() + per)
            res = _attempt2(N, k, d, D, M, rng, att)
            if res is None:
                continue
            T, darts = res
            consider(2 * k * N, _edges2(N, k, T, darts))
            break
        N += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    dl_k2 = start + 0.6 * time_limit
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [(1, [])]

    def consider(n, e):
        if n > best[0][0] and lib.is_valid(n, e, d, D):
            best[0] = (n, e)

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0]

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
        return best[0]

    # Phase 1: two-orbit voltage lifts (new), then Phase 2: one-orbit bi-Cayley.
    _search_k2(d, D, rng, dl_k2, consider, best[0][0])
    _search_k1(d, D, rng, deadline, consider, best[0][0])

    n, e = best[0]
    if not lib.is_valid(n, e, d, D):
        return 1, []
    return n, e
