import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per order N within one bi-Cayley attempt
ITERS = 800                   # annealing steps per bi-Cayley (group, connection set) try
TOP_SLACK = 8                 # bi-Cayley orders up to Nmax//2 + TOP_SLACK
MAX_GROUPS_LIFT4 = 6          # groups tried per order N in the two-orbit lift search
ITERS_LIFT4 = 600             # annealing steps per two-orbit lift try
BICAYLEY_SHARE = 0.35         # fraction of the time budget given to bi-Cayley search


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
# Shared group utilities.
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


def _cayley_tables(N, mul, inv):
    """Multiplication table T[x][g] = x*g and the inverse list for a group of order N."""
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    return T, invs


# ----------------------------------------------------------------------------
# Bi-Cayley search (parent's construction): A_x -- B_{x s} for s in S.
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
    """Try groups of order N until one yields a bi-Cayley graph of diameter <= D, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T, invs = _cayley_tables(N, mul, inv)
        S = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# NEW: two-orbit-per-side voltage lift search.
#
# Base graph has 4 vertices: A_0, A_1 (side A) and B_0, B_1 (side B).
# Voltage block C = [[a, d-a], [d-a, a]] gives A_i and B_j exactly C[i][j]
# darts, so every base vertex has degree d. Each dart (i, j, g) joins
# A_i,x to B_j,(x*g) for all x in the group. The lift has 4N vertices.
# Left multiplication is an automorphism, so distances from the four
# identity-orbit representatives determine the diameter.
# ----------------------------------------------------------------------------

def _unreached4(N, T, invs, V, D):
    """Count (source, vertex) pairs at distance > D over the four orbit representatives."""
    # rowA[i]: darts leaving A_i as (target base index 2+j, voltage g).
    rowA = [[(2 + j, g) for j in range(2) for g in V[i][j]] for i in range(2)]
    # colB[j]: darts leaving B_j as (target base index i, inverse voltage).
    colB = [[(i, invs[g]) for i in range(2) for g in V[i][j]] for j in range(2)]
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(4 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                side, x = divmod(u, N)
                row = rowA[side] if side < 2 else colB[side - 2]
                row_T = T[x]
                for tgt, h in row:
                    v = tgt * N + row_T[h]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 4 * N - count
    return total


def _anneal4(N, T, invs, d, a, D, rng, iters, deadline):
    """Anneal distinct voltages per block so that all 4N vertices are within distance D."""
    C = [[a, d - a], [d - a, a]]
    V = [[rng.sample(range(N), C[i][j]) for j in range(2)] for i in range(2)]
    blocks = [(i, j) for i in range(2) for j in range(2) if C[i][j] > 0]
    cur = _unreached4(N, T, invs, V, D)
    for it in range(iters):
        if cur == 0:
            return V
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i, j = blocks[rng.randrange(len(blocks))]
        s = rng.randrange(len(V[i][j]))
        c = rng.randrange(N)
        if c in V[i][j]:
            continue
        old = V[i][j][s]
        V[i][j][s] = c
        v = _unreached4(N, T, invs, V, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            V[i][j][s] = old
    return V if cur == 0 else None


def _attempt4(N, d, D, rng, deadline):
    """Try groups of order N for the two-orbit lift; return (order, mul, V) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    alist = list(range(1, d // 2 + 1))   # a and d-a give isomorphic lifts
    for m, k, r in groups[:MAX_GROUPS_LIFT4]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T, invs = _cayley_tables(N, mul, inv)
        a = rng.choice(alist)
        V = _anneal4(N, T, invs, d, a, D, rng, ITERS_LIFT4, deadline)
        if V is not None:
            return order, mul, V
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    split = start + BICAYLEY_SHARE * time_limit
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
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    # Phase 1: bi-Cayley search over semidirect products (2N vertices).
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + TOP_SLACK)
    cands = set(range(d + 1, top + 1))

    budget = 0.4
    while time.monotonic() < split and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= split:
                break
            att_deadline = min(split, now + budget)
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

    # Phase 2: two-orbit-per-side voltage lifts (4N vertices). Only orders
    # that beat the current best are worth trying.
    hi = lib._moore_bound(d, D) // 4
    lo = max(d + 1, best_n // 4 + 1)
    if lo <= hi:
        budget = 0.3
        while time.monotonic() < deadline:
            for N in range(lo, hi + 1):
                now = time.monotonic()
                if now >= deadline:
                    break
                if 4 * N <= best_n:
                    continue
                res = _attempt4(N, d, D, rng, min(deadline, now + budget))
                if res is None:
                    continue
                order, mul, V = res
                darts = [(i, 2 + j, g) for i in range(2) for j in range(2) for g in V[i][j]]
                n, e = lib.group_lift(4, darts, order, mul)
                consider(n, e)
            budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
