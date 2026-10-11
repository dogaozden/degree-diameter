import itertools
import math
import random
import time

import lib

# ---- phase 2 (bi-Cayley, inherited from parent) ----
MAX_GROUPS_PER_ATTEMPT = 12
ITERS = 600
T_HOT = 1.5
T_COLD = 0.15
WINDOW_FRAC = 0.95
BUDGET_START = 0.4
BUDGET_CAP = 3.0

# ---- phase 1 (new: 2-by-2 multi-base lifts over semidirect groups) ----
MAX_GROUPS_4 = 8
ITERS_4 = 500
T4_HOT = 3.0
T4_COLD = 0.3
BUDGET_4 = 2.0
PHASE1_FRAC = 0.75


# ----------------------------------------------------------------------------
# Baseline families (always valid when they pass lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
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
# Shared helpers
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


# ----------------------------------------------------------------------------
# Phase 1: 2+2 base lift. Base vertices A0, A1, B0, B1. Dart counts form
# [[a, d-a], [d-a, a]], so every base vertex has degree d. Each dart carries a
# voltage in G (distinct within a block), and the lift is
# (A_i, x) -- (B_j, x*g). Left multiplication is an automorphism, so the four
# sources (A0, A1, B0, B1 at identity) decide the diameter.
# ----------------------------------------------------------------------------

def _unreached4(N, T, invs, vol, D):
    darts_from = [[], []]
    darts_into = [[], []]
    for i in (0, 1):
        for j in (0, 1):
            for g in vol[i][j]:
                darts_from[i].append((j, g))
                darts_into[j].append((i, invs[g]))
    M = 4 * N
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(M)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < 2 * N:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in darts_from[i]:
                        v = (2 + j) * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - 2 * N, N)
                    row = T[y]
                    for i, h in darts_into[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += M - count
    return total


def _anneal4(N, T, invs, d, D, rng, iters, deadline):
    a = rng.randrange(1, d)
    sizes = [[a, d - a], [d - a, a]]
    vol = [[rng.sample(range(N), sizes[i][j]) for j in (0, 1)] for i in (0, 1)]
    cur = _unreached4(N, T, invs, vol, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T4_HOT * (T4_COLD / T4_HOT) ** (it / iters)
        i = rng.randrange(2)
        j = rng.randrange(2)
        lst = vol[i][j]
        p = rng.randrange(len(lst))
        c = rng.randrange(N)
        if c in lst:
            continue
        old = lst
        new = lst[:]
        new[p] = c
        vol[i][j] = new
        v = _unreached4(N, T, invs, vol, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            vol[i][j] = old
    return vol if cur == 0 else None


def _attempt4(N, d, D, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_4]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        vol = _anneal4(N, T, invs, d, D, rng, ITERS_4, deadline)
        if vol is not None:
            return N, T, vol
    return None


def _edges4(N, T, vol):
    E = []
    for i in (0, 1):
        for j in (0, 1):
            for g in vol[i][j]:
                for x in range(N):
                    E.append((i * N + x, (2 + j) * N + T[x][g]))
    return 4 * N, E


# ----------------------------------------------------------------------------
# Phase 2: bi-Cayley over semidirect products (parent's method).
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


def _anneal(N, T, invs, d, D, rng, iters, deadline):
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
# Driver
# ----------------------------------------------------------------------------

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

    moore = lib.moore_bound(d, D)

    # ---- Phase 1: 2+2 base lifts over non-cyclic semidirect groups ----
    total = deadline - start
    p1 = start + PHASE1_FRAC * total
    hi4 = moore // 4
    while time.monotonic() < p1:
        lo4 = max(d + 1, best_n // 4 + 1)
        if lo4 > hi4:
            break
        N = rng.randint(lo4, hi4)
        now = time.monotonic()
        res = _attempt4(N, d, D, rng, min(p1, now + BUDGET_4))
        if res is None:
            continue
        N, T, vol = res
        n, e = _edges4(N, T, vol)
        consider(n, e)

    # ---- Phase 2: bi-Cayley search (parent's method) ----
    Nmax = moore // 2
    top = min(Nmax, Nmax // 2 + 6)
    if top >= d + 1:
        floor = max(d + 1, int(WINDOW_FRAC * top))
        budget = BUDGET_START
        while time.monotonic() < deadline:
            lo = max(floor, best_n // 2 + 1)
            cands = list(range(lo, top + 1))
            if not cands:
                break
            rng.shuffle(cands)
            success = False
            for N in cands:
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
                success = True
                break
            if not success:
                if budget < BUDGET_CAP:
                    budget = min(BUDGET_CAP, budget * 1.5)
                elif floor > d + 1:
                    floor -= 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
