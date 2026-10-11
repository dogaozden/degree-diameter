import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # bi-Cayley: groups tried per order N within one attempt
ITERS = 800                   # bi-Cayley: annealing steps per (group, connection set)
TOP_SLACK = 8                 # bi-Cayley: search orders up to Nmax//2 + TOP_SLACK

LIFT_A = 2                    # base graph has LIFT_A vertices per side
LIFT_GROUPS = 12              # lift: groups tried per order N within one attempt
LIFT_ITERS = 600              # lift: annealing steps per (group) try
BI_PHASE_FRAC = 0.35          # fraction of remaining time spent on bi-Cayley first


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
# Group helpers.
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
# Phase 1: bi-Cayley search (single base vertex per side), as in the parent.
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


def _bi_attempt(N, d, D, rng, deadline):
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


def _bi_phase(d, D, rng, end, consider):
    """Bi-Cayley search: orders tried from large to small with growing budgets, until end."""
    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    top = min(Nmax, Nmax // 2 + TOP_SLACK)
    cands = set(range(d + 1, top + 1))

    budget = 0.4
    while time.monotonic() < end and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= end:
                break
            att_deadline = min(end, now + budget)
            res = _bi_attempt(N, d, D, rng, att_deadline)
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


# ----------------------------------------------------------------------------
# Phase 2 (bold): bipartite voltage lifts over non-cyclic groups.
#
# Base graph: LIFT_A "A" vertices and LIFT_A "B" vertices, each of degree d.
# A-slot s = i*d + t carries a dart (J[s], G[s]): it joins A(i,x) to
# B(J[s], x*G[s]) for every group element x. Each B-layer j receives exactly
# d slots (so B has degree d), and (j, g) pairs are distinct within each i
# (so the lift is simple). Left multiplication is an automorphism, so
# eccentricities are checked from one source per layer.
# ----------------------------------------------------------------------------

def _lift_cost(N, a, d, D, T, invs, J, G):
    """Count (source, vertex) pairs at distance > D over one source per layer."""
    aN = a * N
    V = 2 * aN
    darts = [[] for _ in range(a)]
    Bnb = [[] for _ in range(a)]
    for s in range(a * d):
        i = s // d
        j = J[s]
        g = G[s]
        darts[i].append((j, g))
        Bnb[j].append((i, invs[g]))
    total = 0
    sources = list(range(0, aN, N)) + list(range(aN, V, N))
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < aN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in darts[i]:
                        v = aN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - aN, N)
                    row = T[y]
                    for i, h in Bnb[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _dup_free(a, d, J, G):
    """True if, within each A-layer, the (j, g) pairs are pairwise distinct."""
    for i in range(a):
        seen = set()
        for t in range(d):
            s = i * d + t
            key = (J[s], G[s])
            if key in seen:
                return False
            seen.add(key)
    return True


def _lift_anneal(N, a, d, D, T, invs, rng, deadline):
    """Anneal dart labels (J, G) to zero unreached pairs; return (J, G) or None."""
    S = a * d
    J = G = None
    for _ in range(50):
        J = [j for j in range(a) for _ in range(d)]
        rng.shuffle(J)
        G = [rng.randrange(N) for _ in range(S)]
        if _dup_free(a, d, J, G):
            break
    else:
        return None

    cur = _lift_cost(N, a, d, D, T, invs, J, G)
    for it in range(LIFT_ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / LIFT_ITERS))
        if rng.random() < 0.5:
            s1 = rng.randrange(S)
            s2 = rng.randrange(S)
            if J[s1] == J[s2]:
                continue
            J[s1], J[s2] = J[s2], J[s1]
            kind, old = 0, (s1, s2)
        else:
            s = rng.randrange(S)
            newg = rng.randrange(N)
            if newg == G[s]:
                continue
            old = G[s]
            G[s] = newg
            kind = 1
        if not _dup_free(a, d, J, G):
            if kind == 0:
                s1, s2 = old
                J[s1], J[s2] = J[s2], J[s1]
            else:
                G[s] = old
            continue
        v = _lift_cost(N, a, d, D, T, invs, J, G)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            if kind == 0:
                s1, s2 = old
                J[s1], J[s2] = J[s2], J[s1]
            else:
                G[s] = old
    if cur == 0:
        return J, G
    return None


def _lift_attempt(N, a, d, D, rng, deadline):
    """Try non-cyclic groups of order N = 2aN-lift candidates until one works."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:LIFT_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        res = _lift_anneal(N, a, d, D, T, invs, rng, deadline)
        if res is not None:
            return T, res
    return None


def _lift_edges(N, a, d, T, J, G):
    """Expand a lift solution to (n, edges)."""
    aN = a * N
    edges = []
    for s in range(a * d):
        i = s // d
        j = J[s]
        g = G[s]
        for x in range(N):
            edges.append((i * N + x, aN + j * N + T[x][g]))
    return 2 * aN, edges


def _lift_phase(d, D, rng, end, consider, get_best_n):
    """Ascending search for lifts; each success raises the bar to the next order."""
    a = LIFT_A
    hi = lib._moore_bound(d, D) // (2 * a)
    budget = 0.5
    N_cur = get_best_n() // (2 * a) + 1
    while time.monotonic() < end:
        lo = max(d + 1, get_best_n() // (2 * a) + 1)
        if N_cur < lo:
            N_cur = lo
        if N_cur > hi:
            N_cur = lo
            budget *= 1.5
            if lo > hi:
                return
            continue
        now = time.monotonic()
        att_end = min(end, now + budget)
        res = _lift_attempt(N_cur, a, d, D, rng, att_end)
        if res is not None:
            T, (J, G) = res
            n, edges = _lift_edges(N_cur, a, d, T, J, G)
            consider(n, edges)
        N_cur += 1


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    # Phase 1: bi-Cayley search gives a safe baseline.
    now = time.monotonic()
    bi_end = now + BI_PHASE_FRAC * (deadline - now)
    _bi_phase(d, D, rng, bi_end, consider)

    # Phase 2: bold voltage lifts over non-cyclic groups, aiming past the baseline.
    if d >= 3 and D >= 2 and time.monotonic() < deadline:
        _lift_phase(d, D, rng, deadline, consider, lambda: best_n)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
