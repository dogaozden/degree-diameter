import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per order N within one bi-Cayley attempt
ITERS = 400                   # annealing steps per (group, connection set) try

LIFT_GROUPS = 8               # groups tried per order N in the 2x2-base lift search
LIFT_ITERS = 300              # annealing steps per (group) try in the lift search
LIFT_BUDGET = 2.0             # seconds spent on each order N in the lift search


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
# NEW: 2x2-base group lift search.
#
# Base bipartite multigraph with A-vertices a in {0,1} and B-vertices b in {0,1}.
# A dart (a, b, g) joins A(a,x) to B(b, x*g) for every x in G. Multiplicities
#   [[s, d-s], [d-s, s]]
# make every base vertex have degree d, so the lift is d-regular on 4|G| vertices.
# Left multiplication by G is an automorphism, so eccentricities need only be
# checked from the four fibre identities. This generalises the single-fibre
# bi-Cayley search and gives 4N vertices instead of 2N.
#
# Encoding: A(a,x) = a*N + x ; B(b,y) = 2N + b*N + y.
# ----------------------------------------------------------------------------

def _unreached2(N, T, invs, darts, D):
    """Count (source, vertex) pairs not within distance D, sources = fibre identities."""
    outA = [[], []]
    inB = [[], []]
    for a, b, g in darts:
        outA[a].append((b, g))
        inB[b].append((a, invs[g]))
    V = 4 * N
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < 2 * N:
                    a, x = divmod(u, N)
                    row = T[x]
                    for b, g in outA[a]:
                        v = 2 * N + b * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    b, y = divmod(u - 2 * N, N)
                    row = T[y]
                    for a, h in inB[b]:
                        v = a * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _darts_of(blocks):
    """Flatten blocks [a, b, elements] into a dart list [(a, b, g), ...]."""
    return [(a, b, g) for a, b, els in blocks for g in els]


def _anneal2(N, T, invs, s, d, D, rng, iters, deadline):
    """Anneal the dart elements of the four blocks to zero unreached pairs."""
    shape = [(0, 0, s), (0, 1, d - s), (1, 0, d - s), (1, 1, s)]
    shape = [(a, b, c) for a, b, c in shape if c > 0]
    blocks = [[a, b, rng.sample(range(N), c)] for a, b, c in shape]
    cur = _unreached2(N, T, invs, _darts_of(blocks), D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        bi = rng.randrange(len(blocks))
        els = blocks[bi][2]
        j = rng.randrange(len(els))
        c = rng.randrange(N)
        if c in els:
            continue
        old = els[j]
        els[j] = c
        v = _unreached2(N, T, invs, _darts_of(blocks), D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            els[j] = old
    return _darts_of(blocks) if cur == 0 else None


def _attempt2(N, d, D, rng, deadline):
    """Try groups of order N for the 2x2-base lift. Return (T, darts) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:LIFT_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        s = rng.randint(1, d - 1)
        darts = _anneal2(N, T, invs, s, d, D, rng, LIFT_ITERS, deadline)
        if darts is not None:
            return T, darts
    return None


def _lift2_edges(N, T, darts):
    """Edges of the 2x2-base lift: 4N vertices, A(a,x)=a*N+x, B(b,y)=2N+b*N+y."""
    edges = []
    for a, b, g in darts:
        for x in range(N):
            edges.append((a * N + x, 2 * N + b * N + T[x][g]))
    return edges


# ----------------------------------------------------------------------------
# Bi-Cayley search over semidirect products (parent construction, unchanged).
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
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

    # NEW phase: 2x2-base group lift search (4N vertices). Ascending in N,
    # since successes at small N are quick; each N gets a bounded budget.
    lift_deadline = start + 0.5 * time_limit
    Nmax2 = lib._moore_bound(d, D) // 4
    N = max(d + 1, best_n // 4 + 1)
    while N <= Nmax2 and time.monotonic() < lift_deadline:
        att = min(lift_deadline, time.monotonic() + LIFT_BUDGET)
        res = _attempt2(N, d, D, rng, att)
        if res is not None:
            T, darts = res
            consider(4 * N, _lift2_edges(N, T, darts))
        N += 1

    # Parent phase: bi-Cayley search for the remaining time.
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + 3)
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
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
