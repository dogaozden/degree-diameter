import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per order N within one 2-orbit attempt
ITERS = 400                   # annealing steps per (group, connection set) try for 2-orbit
MAX_GROUPS4 = 10              # groups tried per order N for the 4-orbit lift
ITERS4 = 600                  # annealing steps per try for the 4-orbit lift
FOUR_TOP = 100                # largest group order N explored by the 4-orbit search
FOUR_SHARE = 0.5              # fraction of the time budget given to the 4-orbit search


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
# NEW: 4-orbit bi-Cayley lift.
#
# Two base vertices on each side: A_0, A_1 and B_0, B_1, each blown up into a
# copy of G. Cell (i, j) carries a connection set S[i][j] of group elements,
# and A_i,x is joined to B_j,(x*g) for g in S[i][j]. Left multiplication by G
# is an automorphism, so the diameter is decided by four sources: A_0, A_1,
# B_0, B_1 at the identity. Degrees force |S00| = |S11| = a and
# |S01| = |S10| = d - a, with 1 <= a <= d-1 so the graph is connected.
# This gives 4N vertices, so beating 336 needs N >= 85.
# ----------------------------------------------------------------------------

def _cost4(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for the four base sources."""
    n4 = 4 * N
    Sinv = [[[invs[g] for g in S[i][j]] for j in range(2)] for i in range(2)]
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(n4)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < 2 * N:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j in (0, 1):
                        base = 2 * N + j * N
                        for g in S[i][j]:
                            v = base + row[g]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                else:
                    j, y = divmod(u - 2 * N, N)
                    row = T[y]
                    for i in (0, 1):
                        base = i * N
                        for h in Sinv[i][j]:
                            v = base + row[h]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += n4 - count
    return total


def _anneal4(N, T, invs, a, d, D, rng, iters, deadline):
    """Simulated annealing over the four connection sets to zero unreached pairs."""
    sizes = [[a, d - a], [d - a, a]]
    S = [[rng.sample(range(N), sizes[i][j]) for j in range(2)] for i in range(2)]
    cur = _cost4(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(2)
        j = rng.randrange(2)
        k = rng.randrange(sizes[i][j])
        c = rng.randrange(N)
        if c in S[i][j]:
            continue
        S2 = [[list(S[p][q]) for q in range(2)] for p in range(2)]
        S2[i][j][k] = c
        v = _cost4(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _attempt4(N, d, D, rng, deadline):
    """Try groups of order N for the 4-orbit lift until one yields diameter <= D."""
    if d < 2:
        return None
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS4]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        a = rng.randint(1, d - 1)
        S = _anneal4(N, T, invs, a, d, D, rng, ITERS4, deadline)
        if S is not None:
            return T, S
    return None


def _edges4(N, T, S):
    """Edge list of the 4-orbit lift: A_i,x -- B_j,T[x][g]; A vertices 0..2N-1, B vertices 2N..4N-1."""
    edges = []
    for i in (0, 1):
        for j in (0, 1):
            for x in range(N):
                row = T[x]
                for g in S[i][j]:
                    edges.append((i * N + x, 2 * N + j * N + row[g]))
    return edges


def _search_four(d, D, rng, deadline):
    """Adaptive search: sample orders N, and after each success only accept larger ones."""
    Nmax = lib._moore_bound(d, D) // 4
    lo = d + 1
    hi = min(Nmax, FOUR_TOP)
    best = None
    budget = 0.5
    while time.monotonic() < deadline and lo <= hi:
        N = rng.randint(lo, hi)
        att = min(deadline, time.monotonic() + budget)
        res = _attempt4(N, d, D, rng, att)
        if res is None:
            budget = min(budget * 1.1, 3.0)
            continue
        T, S = res
        edges = _edges4(N, T, S)
        if lib.is_valid(4 * N, edges, d, D):
            best = (4 * N, edges)
        lo = N + 1
    return best


# ----------------------------------------------------------------------------
# Bi-Cayley search over semidirect products Z_m x| Z_k of order N (2 orbits).
#
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


def _bicayley_search(d, D, rng, deadline):
    """Parent's 2-orbit bi-Cayley search; returns the largest valid (n, edges) found or None."""
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + 3)
    cands = set(range(d + 1, top + 1))
    if not cands:
        return None
    budget = 0.4
    best = None
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
            if lib.is_valid(2 * N, edges, d, D):
                if best is None or 2 * N > best[0]:
                    best = (2 * N, edges)
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 2
    return best


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

    # New 4-orbit lift gets the first share of the search time.
    split = start + FOUR_SHARE * (deadline - start)
    r4 = _search_four(d, D, rng, split)
    if r4 is not None:
        consider(r4[0], r4[1])

    # Parent's 2-orbit search uses the rest.
    r2 = _bicayley_search(d, D, rng, deadline)
    if r2 is not None:
        consider(r2[0], r2[1])

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
