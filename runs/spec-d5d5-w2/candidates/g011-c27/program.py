import itertools
import math
import random
import time

import lib

# Phase 1: voltage lifts of a 2-vertex-per-side base graph over semidirect groups.
BASE = 2
LIFT_ITERS = 500
LIFT_T_HOT = 3.0
LIFT_T_COLD = 0.2
LIFT_BUDGET_START = 0.8
LIFT_BUDGET_CAP = 4.0
LIFT_GROUPS = 12

# Phase 2: bi-Cayley search (baseline family, used with leftover time).
MAX_GROUPS_PER_ATTEMPT = 12
ITERS = 600
T_HOT = 1.5
T_COLD = 0.15
WINDOW_FRAC = 0.95
BUDGET_START = 0.4
BUDGET_CAP = 3.0


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
# Groups of order N as semidirect products Z_m x| Z_k.
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
# Phase 1: 2-base voltage lifts over a group G of order N.
#
# Vertices A_{i,x} (i < BASE, x in G) and B_{j,y}. For each base pair (i, j)
# there are M[i][j] darts with distinct voltages g, giving edges
# A_{i,x} -- B_{j, x g}. Left multiplication by h is an automorphism, so the
# diameter check only needs BFS from A_{i,e} and B_{j,e}.
# Degrees: row sums and column sums of M equal d; M = [[a, d-a], [d-a, a]].
# ----------------------------------------------------------------------------

def _lift_cost(N, b, T, V, D):
    """Count (source, vertex) pairs not within distance D over the base sources."""
    Vt = 2 * b * N
    adj = [[] for _ in range(Vt)]
    for i in range(b):
        aoff = i * N
        for j in range(b):
            boff = b * N + j * N
            for g in V[i][j]:
                for x in range(N):
                    a = aoff + x
                    c = boff + T[x][g]
                    adj[a].append(c)
                    adj[c].append(a)
    sources = [i * N for i in range(b)] + [b * N + j * N for j in range(b)]
    total = 0
    for src in sources:
        seen = bytearray(Vt)
        seen[src] = 1
        reached = 1
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
            reached += len(nxt)
            frontier = nxt
        total += Vt - reached
    return total


def _lift_anneal(N, T, b, d, D, rng, deadline):
    """Anneal the voltages of a 2-base lift to zero unreached pairs."""
    a = rng.randrange(1, d)   # d >= 2
    M = [[a, d - a], [d - a, a]]
    V = [[rng.sample(range(N), M[i][j]) for j in range(b)] for i in range(b)]
    cur = _lift_cost(N, b, T, V, D)
    for it in range(LIFT_ITERS):
        if cur == 0:
            return V
        if time.monotonic() > deadline:
            break
        temp = LIFT_T_HOT * (LIFT_T_COLD / LIFT_T_HOT) ** (it / LIFT_ITERS)
        i = rng.randrange(b)
        j = rng.randrange(b)
        t = rng.randrange(len(V[i][j]))
        g = rng.randrange(N)
        if g in V[i][j]:
            continue
        old = V[i][j][t]
        V[i][j][t] = g
        v = _lift_cost(N, b, T, V, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            V[i][j][t] = old
    if cur == 0:
        return V
    return None


def _lift_attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a valid 2-base lift, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:LIFT_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _order, mul, _inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        V = _lift_anneal(N, T, BASE, d, D, rng, deadline)
        if V is not None:
            return T, V
    return None


def _lift_edges(N, b, T, V):
    """Expand a 2-base lift into (vertex count, edge list)."""
    edges = []
    for i in range(b):
        for j in range(b):
            for g in V[i][j]:
                for x in range(N):
                    edges.append((i * N + x, b * N + j * N + T[x][g]))
    return 2 * b * N, edges


# ----------------------------------------------------------------------------
# Phase 2: bi-Cayley search over semidirect products (parent's method).
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

    # Phase 1: 2-base voltage lifts. Order N gives 2*BASE*N vertices.
    lift_end = start + 0.6 * (deadline - start)
    Nhi = lib._moore_bound(d, D) // (2 * BASE)
    if Nhi >= 2:
        floor = max(2, Nhi // 2)
        budget = LIFT_BUDGET_START
        while time.monotonic() < lift_end:
            lo = max(floor, best_n // (2 * BASE) + 1)
            if lo > Nhi:
                break
            cands = list(range(lo, Nhi + 1))
            rng.shuffle(cands)
            success = False
            for N in cands:
                now = time.monotonic()
                if now >= lift_end:
                    break
                att_deadline = min(lift_end, now + budget)
                res = _lift_attempt(N, d, D, rng, att_deadline)
                if res is None:
                    continue
                T, V = res
                n, e = _lift_edges(N, BASE, T, V)
                consider(n, e)
                success = True
                break
            if not success:
                if budget < LIFT_BUDGET_CAP:
                    budget = min(LIFT_BUDGET_CAP, budget * 1.5)
                elif floor > 2:
                    floor -= 1

    # Phase 2: bi-Cayley search with the remaining time.
    if d >= 2 and D >= 2 and time.monotonic() < deadline:
        Nmax = lib._moore_bound(d, D) // 2
        top = min(Nmax, Nmax // 2 + 6)
        if top >= d + 1:
            floor = max(d + 1, int(WINDOW_FRAC * top))
            bestN = 0
            budget = BUDGET_START
            while time.monotonic() < deadline:
                lo = max(floor, bestN + 1)
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
                    bestN = max(bestN, N)
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
