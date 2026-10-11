import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per order within one attempt
ITERS_1 = 400                 # annealing steps for the 1x1 bi-Cayley search
ITERS_2 = 1200                # annealing steps for the 2x2 base search


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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group enumeration: semidirect products Z_m x|_r Z_k of order N.
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
# Phase 1: 1x1 bi-Cayley search (A_x -- B_{xs}, s in S), order 2N.
# ----------------------------------------------------------------------------

def _unreached_1(N, T, invs, S, D):
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


def _anneal_1(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached_1(N, T, invs, S, D)
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
        v = _unreached_1(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _attempt_1(N, d, D, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal_1(N, T, invs, d, D, rng, ITERS_1, deadline)
        if S is not None:
            return T, S
    return None


def _search_1x1(d, D, rng, deadline, consider):
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
            res = _attempt_1(N, d, D, rng, att_deadline)
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
            budget = min(budget * 2, 8.0)


# ----------------------------------------------------------------------------
# Phase 2 (new construction): 2x2 base bi-Cayley lift over a group G of order N.
#
# Vertices: A_{i,x} = i*N + x, B_{j,y} = 2N + j*N + y, i, j in {0, 1}.
# Block (i, j) carries a connection set S_ij in G with edges
#     A_{i,x} -- B_{j, x*s}   for s in S_ij.
# Sizes: |S_00| = |S_11| = a, |S_01| = |S_10| = d - a, with 1 <= a <= d-1, so every
# vertex has degree d. Left multiplication by G is an automorphism, so the
# eccentricity of every vertex equals that of one of the four sources A_0, A_1, B_0, B_1.
# Order = 4N, bipartite by construction.
# ----------------------------------------------------------------------------

def _cost_2(N, T, invs, conn, D):
    nv = 4 * N
    adj = [None] * nv
    for i in (0, 1):
        for x in range(N):
            row = T[x]
            lst = []
            for j in (0, 1):
                base = 2 * N + j * N
                for s in conn[i][j]:
                    lst.append(base + row[s])
            adj[i * N + x] = lst
    for j in (0, 1):
        for y in range(N):
            row = T[y]
            lst = []
            for i in (0, 1):
                base = i * N
                for s in conn[i][j]:
                    lst.append(base + row[invs[s]])
            adj[2 * N + j * N + y] = lst
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(nv)
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
        total += nv - count
    return total


def _anneal_2(N, T, invs, d, D, rng, iters, deadline):
    a = rng.randint(1, d - 1)
    sizes = [[a, d - a], [d - a, a]]
    conn = [[rng.sample(range(N), sizes[i][j]) for j in (0, 1)] for i in (0, 1)]
    cur = _cost_2(N, T, invs, conn, D)
    for it in range(iters):
        if cur == 0:
            return conn
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(2)
        j = rng.randrange(2)
        block = conn[i][j]
        pos = rng.randrange(len(block))
        c = rng.randrange(N)
        if c in block:
            continue
        old = block[pos]
        block[pos] = c
        v = _cost_2(N, T, invs, conn, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            block[pos] = old
    return conn if cur == 0 else None


def _attempt_2(N, d, D, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        conn = _anneal_2(N, T, invs, d, D, rng, ITERS_2, deadline)
        if conn is not None:
            return T, invs, conn
    return None


def _edges_2(N, T, conn):
    E = []
    for i in (0, 1):
        for j in (0, 1):
            base = 2 * N + j * N
            for s in conn[i][j]:
                for x in range(N):
                    E.append((i * N + x, base + T[x][s]))
    return 4 * N, E


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget_total = 0.8 * time_limit
    deadline = start + budget_total
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

    # Phase 1: short 1x1 bi-Cayley search as a safe baseline.
    phase1_deadline = start + 0.25 * budget_total
    _search_1x1(d, D, rng, phase1_deadline, consider)

    # Phase 2: 2x2 base lifts, aiming for order 4N > best_n.
    N = max(d, best_n // 4 + 1)
    budget = 0.5
    while time.monotonic() < deadline:
        now = time.monotonic()
        att_deadline = min(deadline, now + budget)
        res = _attempt_2(N, d, D, rng, att_deadline)
        if res is None:
            budget = min(budget * 1.5, 8.0)
            continue
        T, invs, conn = res
        n, e = _edges_2(N, T, conn)
        consider(n, e)
        N = max(N + 1, best_n // 4 + 1)
        budget = 0.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
