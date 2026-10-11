import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per order N within one bi-Cayley attempt
ITERS = 400                   # annealing steps per (group, connection set) try
MULTI_GROUPS = 3              # groups tried per order N in the multi-orbit search
MULTI_ITERS = 700             # annealing steps per multi-orbit try


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
# Groups: semidirect products Z_m x|_r Z_k of order N.
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
# Single-orbit bi-Cayley search (A_x -- B_{xs}, s in S, |S| = d).
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
# NEW: multi-orbit bi-Cayley lift (2 A-orbits, 2 B-orbits, group of order N).
#
# Vertices A_{i,x} = i*N + x (i in {0,1}), B_{j,y} = (2+j)*N + y.
# A dart (i, j, g) joins A_{i,x} to B_{j, x*g} for every x in G, so each
# dart lifts to a perfect matching between orbit i and orbit j.
# The count matrix C = [[a, d-a], [d-a, a]] gives every vertex degree d.
# Left multiplication by G is an automorphism, so the diameter is checked
# by BFS from the four orbit identities only. The result has 4N vertices,
# so it can beat a single-orbit bi-Cayley graph of the same degree.
# ----------------------------------------------------------------------------

def _multi_adj(N, p, darts, T):
    """Adjacency lists of the multi-orbit lift described by darts (i, j, g)."""
    V = 2 * p * N
    adj = [[] for _ in range(V)]
    for i, j, g in darts:
        base_a = i * N
        base_b = (p + j) * N
        for x in range(N):
            a = base_a + x
            b = base_b + T[x][g]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _multi_unreached(N, p, darts, T, D):
    """Count (source, vertex) pairs at distance > D, over the 2p orbit identities."""
    V = 2 * p * N
    adj = _multi_adj(N, p, darts, T)
    total = 0
    for src in range(0, V, N):
        seen = bytearray(V)
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
        total += V - count
    return total


def _multi_anneal(N, p, counts, T, D, rng, iters, deadline):
    """Anneal the dart voltages; counts is a list of (i, j, c) with c distinct voltages per block."""
    darts = []
    for i, j, c in counts:
        for g in rng.sample(range(N), c):
            darts.append([i, j, g])
    cur = _multi_unreached(N, p, darts, T, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        k = rng.randrange(len(darts))
        i, j, old = darts[k]
        g = rng.randrange(N)
        if any(a == i and b == j and h == g for a, b, h in darts):
            continue
        darts[k][2] = g
        v = _multi_unreached(N, p, darts, T, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[k][2] = old
    return darts if cur == 0 else None


def _multi_attempt(N, p, d, D, rng, deadline):
    """Try semidirect groups of order N for a 2x2 multi-orbit lift of degree d."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MULTI_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        a = rng.randrange(1, d)
        counts = [(0, 0, a), (0, 1, d - a), (1, 0, d - a), (1, 1, a)]
        darts = _multi_anneal(N, p, counts, T, D, rng, MULTI_ITERS, deadline)
        if darts is not None:
            return T, darts
    return None


def _multi_edges(N, p, darts, T):
    """Expand darts into the edge list of the multi-orbit lift."""
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, (p + j) * N + T[x][g]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
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
    if D >= 4 and time.monotonic() < start + 0.4 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    # Phase 1: single-orbit bi-Cayley search over semidirect products.
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + 3)
    cands = set(range(d + 1, top + 1))
    budget = 0.4
    phase1 = start + 0.45 * time_limit
    while time.monotonic() < phase1 and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= phase1:
                break
            att_deadline = min(phase1, now + budget)
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

    # Phase 2: multi-orbit (2x2 voltage) lift search, aiming above the current best.
    p = 2
    phase2 = start + 0.85 * time_limit
    Nhi = lib._moore_bound(d, D) // (2 * p)
    budget = 2.0
    while time.monotonic() < phase2:
        lo = best_n // (2 * p) + 1
        if lo > Nhi:
            break
        success = False
        for N in range(lo, Nhi + 1):
            if time.monotonic() >= phase2:
                break
            att = min(phase2, time.monotonic() + budget)
            res = _multi_attempt(N, p, d, D, rng, att)
            if res is None:
                continue
            T, darts = res
            consider(2 * p * N, _multi_edges(N, p, darts, T))
            success = True
            break
        if not success:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
