import itertools
import math
import random
import time

import lib

ORBITS = 2              # bi-Cayley with two orbits per side: 4N vertices
TOP_SLACK = 8
ITERS_SINGLE = 800      # annealing steps, single-orbit phase (parent-style)
ITERS_MULTI = 350       # annealing steps, two-orbit phase
MAX_GROUPS_SINGLE = 30
GROUPS_PER_N = 12       # groups tried per order N in the two-orbit phase
SLICE = 2.5             # seconds per candidate N in the two-orbit phase
PHASE1_FRAC = 0.25      # share of time for the single-orbit fallback search
TOTAL_FRAC = 0.85


# ----------------------------------------------------------------------------
# Baseline families (always validated before use).
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Groups: semidirect products Z_m x|_r Z_k of order N.
# ----------------------------------------------------------------------------

def _groups(N):
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
# Phase 1: single-orbit bi-Cayley search (parent family, used as fallback).
# Vertices A_x, B_y; edge A_x -- B_{x s} for s in S, |S| = d, identity in S.
# ----------------------------------------------------------------------------

def _unreached(N, T, invs, S, D):
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


def _anneal_single(N, T, invs, d, D, rng, iters, deadline):
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


def _attempt_single(N, d, D, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_SINGLE]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal_single(N, T, invs, d, D, rng, ITERS_SINGLE, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Phase 2 (bold change): two-orbit bi-Cayley graphs.
# A-side orbits A_{i,x}, B-side orbits B_{j,y}, i, j in {0, 1}, x, y in G.
# Edges A_{i,x} -- B_{j, x s} for s in S[i][j]. Each A-orbit row sums to d and
# each B-orbit column sums to d, so degrees are exactly d. Left multiplication
# by G is an automorphism, so BFS from the four orbit representatives
# (identities) decides the diameter. Order 4N can exceed the single-orbit range.
# ----------------------------------------------------------------------------

def _adjacency(N, T, S):
    n = 2 * ORBITS * N
    base_b = ORBITS * N
    adj = [[] for _ in range(n)]
    for i in range(ORBITS):
        for x in range(N):
            u = i * N + x
            row = T[x]
            for j in range(ORBITS):
                off = base_b + j * N
                for s in S[i][j]:
                    v = off + row[s]
                    adj[u].append(v)
                    adj[v].append(u)
    return adj


def _bad_pairs_multi(N, adj, D):
    n = 2 * ORBITS * N
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(n)
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
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += n - count
    return total


def _anneal_multi(N, T, S0, D, rng, iters, deadline):
    S = S0
    cur = _bad_pairs_multi(N, _adjacency(N, T, S), D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        i = rng.randrange(ORBITS)
        j = rng.randrange(ORBITS)
        cell = S[i][j]
        k = rng.randrange(len(cell))
        c = rng.randrange(N)
        if c in cell:
            continue
        S2 = [[cs[:] for cs in row] for row in S]
        S2[i][j][k] = c
        v = _bad_pairs_multi(N, _adjacency(N, T, S2), D)
        temp = max(0.5, 20.0 * (1.0 - it / iters))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _attempt_multi(N, d, D, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_N]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        # Degree split: rows and columns of the 2x2 count matrix sum to d.
        p = rng.randint(1, max(1, d // 2))
        sizes = [[p, d - p], [d - p, p]]
        S0 = [[rng.sample(range(N), sizes[i][j]) for j in range(ORBITS)]
              for i in range(ORBITS)]
        S = _anneal_multi(N, T, S0, D, rng, ITERS_MULTI, deadline)
        if S is not None:
            return S, T
    return None


def _multi_edges(N, S, T):
    base_b = ORBITS * N
    edges = []
    for i in range(ORBITS):
        for x in range(N):
            for j in range(ORBITS):
                off = base_b + j * N
                for s in S[i][j]:
                    edges.append((i * N + x, off + T[x][s]))
    return edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + TOTAL_FRAC * time_limit
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

    # Phase 1: single-orbit bi-Cayley fallback (parent family).
    Nmax = moore // 2
    top = min(Nmax, Nmax // 2 + TOP_SLACK)
    cands = set(range(d + 1, top + 1))
    deadline1 = start + PHASE1_FRAC * time_limit
    budget = 0.4
    while time.monotonic() < deadline1 and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= deadline1:
                break
            att_deadline = min(deadline1, now + budget)
            res = _attempt_single(N, d, D, rng, att_deadline)
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

    # Phase 2: two-orbit bi-Cayley graphs of order 4N, ascending N so that
    # every success pushes the order above the current best.
    N_lo = best_n // (ORBITS * 2) + 1
    N_hi = moore // (ORBITS * 2)
    N = max(N_lo, d + 1)
    while N <= N_hi and time.monotonic() < deadline:
        slice_dl = min(deadline, time.monotonic() + SLICE)
        res = _attempt_multi(N, d, D, rng, slice_dl)
        if res is not None:
            S, T = res
            consider(2 * ORBITS * N, _multi_edges(N, S, T))
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
