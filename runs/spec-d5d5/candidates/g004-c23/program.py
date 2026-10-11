import itertools
import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# Parameters
# ----------------------------------------------------------------------------
MAX_GROUPS_PER_ATTEMPT = 12   # bi-Cayley: groups tried per order N
ITERS = 600                   # bi-Cayley: annealing steps per (group, S)
T_HOT = 1.5
T_COLD = 0.15

# New construction: 2-orbit bi-lift (see _bilift_* below).
ITERS2 = 800                  # annealing steps per (group, voltage assignment)
MAX_GROUPS2 = 16              # groups tried per order M within one attempt
TIME_FRAC = 0.85              # fraction of time_limit we are allowed to use
BICAYLEY_FRAC = 0.30          # share of the budget for the bi-Cayley phase


# ----------------------------------------------------------------------------
# Baseline families (fast, validated before use).
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
# Shared: semidirect-product parameters of order N.
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
# Phase A: bi-Cayley search (parent's method). Vertices A_x, B_y, x,y in G,
# edges A_x -- B_{x s} for s in S, |S| = d. Diameter decided from A_0 and B_0.
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


# ----------------------------------------------------------------------------
# Phase B (new): 2-orbit bi-lift over a semidirect group.
#
# Four vertex orbits: A_0, A_1 (left side) and B_0, B_1 (right side), each a
# copy of G with |G| = M, so the graph has 4M vertices. Voltage darts:
#   A_i,x -- B_j, x*g   for each dart (i, j, g).
# The base multigraph is the 2x2 matrix
#     [[a, d-a],
#      [d-a, a]]
# so every vertex gets degree exactly d (a = d // 2). Left multiplication by G
# is an automorphism, so the diameter is decided from the four orbit
# representatives A_0, A_1, B_0, B_1. Voltages inside one (i, j) block are
# kept distinct, so the graph is simple.
#
# Compared with the bi-Cayley search this gives four orbits, hence orders of
# 4M (M >= 85 already beats 336), at the cost of a larger search space.
# ----------------------------------------------------------------------------

def _tables2(ij, gs, invs):
    """Adjacency data per base vertex: outA[i] = [(j, g)], inB[j] = [(i, g^-1)]."""
    outA = [[], []]
    inB = [[], []]
    for (i, j), g in zip(ij, gs):
        outA[i].append((j, g))
        inB[j].append((i, invs[g]))
    return outA, inB


def _cost2(M, T, invs, outA, inB, D):
    """Count unreached (source, vertex) pairs for the four orbit representatives."""
    n = 4 * M
    M2 = 2 * M
    total = 0
    for src in (0, M, M2, M2 + M):
        seen = bytearray(n)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < M2:
                    i = v // M
                    x = v - i * M
                    row = T[x]
                    for j, g in outA[i]:
                        w = M2 + j * M + row[g]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    u = v - M2
                    j = u // M
                    y = u - j * M
                    row = T[y]
                    for i, h in inB[j]:
                        w = i * M + row[h]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += n - count
    return total


def _anneal2(M, T, invs, a, d, D, rng, deadline):
    """Anneal the voltages of the 2x2 base multigraph to zero unreached pairs."""
    spec = [(0, 0, a), (0, 1, d - a), (1, 0, d - a), (1, 1, a)]
    ij, members = [], []
    for i, j, c in spec:
        idx = []
        for _ in range(c):
            idx.append(len(ij))
            ij.append((i, j))
        members.append(idx)
    blk = [0] * d
    for b, idx in enumerate(members):
        for s in idx:
            blk[s] = b

    gs = [0] * d
    for idx in members:
        for s, g in zip(idx, rng.sample(range(M), len(idx))):
            gs[s] = g

    outA, inB = _tables2(ij, gs, invs)
    cur = _cost2(M, T, invs, outA, inB, D)
    for it in range(ITERS2):
        if cur == 0:
            return ij, gs
        if time.monotonic() > deadline:
            return None
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS2)
        t = rng.randrange(d)
        c = rng.randrange(M)
        if any(gs[s] == c for s in members[blk[t]]):
            continue
        old = gs[t]
        gs[t] = c
        outA2, inB2 = _tables2(ij, gs, invs)
        v = _cost2(M, T, invs, outA2, inB2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
            outA, inB = outA2, inB2
        else:
            gs[t] = old
    if cur == 0:
        return ij, gs
    return None


def _attempt2(M, a, d, D, rng, deadline):
    """Try groups of order M for a valid 2-orbit bi-lift; return (T, ij, gs) or None."""
    groups = _groups(M)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS2]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(M)] for x in range(M)]
        invs = [inv(g) for g in range(M)]
        res = _anneal2(M, T, invs, a, d, D, rng, deadline)
        if res is not None:
            return T, res[0], res[1]
    return None


def _edges2(M, T, ij, gs):
    """Expand the voltage assignment into the 4M-vertex graph."""
    M2 = 2 * M
    edges = []
    for (i, j), g in zip(ij, gs):
        base_a = i * M
        base_b = M2 + j * M
        for x in range(M):
            edges.append((base_a + x, base_b + T[x][g]))
    return 4 * M, edges


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + TIME_FRAC * time_limit
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
    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    # ---- Phase A: bi-Cayley search over semidirect products.
    bc_end = start + BICAYLEY_FRAC * time_limit
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + 6)
    cands = set(range(d + 1, top + 1))
    budget = 0.4
    while time.monotonic() < bc_end and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= bc_end:
                break
            att_deadline = min(bc_end, now + budget)
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

    # ---- Phase B: 2-orbit bi-lift. Orders are 4M; only M with 4M > best_n help.
    a = d // 2
    Mmax = lib._moore_bound(d, D) // 4
    lo = max(d, best_n // 4 + 1)
    budget = 4.0
    fails = 0
    while lo <= Mmax and time.monotonic() < end:
        span = min(6, Mmax - lo + 1)
        M = lo + rng.randrange(span)
        att_end = min(end, time.monotonic() + budget)
        res = _attempt2(M, a, d, D, rng, att_end)
        if res is None:
            fails += 1
            if fails % 3 == 0:
                budget *= 1.5
            continue
        T, ij, gs = res
        n, e = _edges2(M, T, ij, gs)
        consider(n, e)
        lo = M + 1
        fails = 0

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
