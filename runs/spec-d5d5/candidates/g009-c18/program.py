import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per (a, N) candidate within one attempt
ITERS = 600                   # annealing steps for the bi-Cayley fallback
LIFT_ITERS = 1500             # annealing steps per voltage-lift try
LIFT_MAX_A = 8                # maximum base vertices per side in a voltage lift
LIFT_MAX_N = 400              # maximum group order used in a voltage lift
T_HOT = 1.5                   # initial annealing temperature (in unreached-pair units)
T_COLD = 0.15                 # final annealing temperature


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
# NEW: general voltage lifts of bipartite base multigraphs with a vertices per side.
#
# Base: a vertices A_i, a vertices B_j, each of degree d (multigraph; parallel
# darts need distinct voltages). Lift over a group G of order N: vertex (v, x)
# for x in G; dart (A_i, B_j, g) joins (A_i, x) to (B_j, x*g).
# Left multiplication is an automorphism of the lift, so the diameter is
# certified by BFS from (v, identity) for each base vertex v. The lift has
# 2*a*N vertices and degree d, so for a = 1 this is the bi-Cayley family.
# ----------------------------------------------------------------------------

def _lift_cost(a, N, darts, T, invs, D):
    """Count (source, vertex) pairs not within distance D, over the 2a fibre identities."""
    out = [[] for _ in range(a)]
    inn = [[] for _ in range(a)]
    for i, j, g in darts:
        out[i].append((j, g))
        inn[j].append((i, invs[g]))
    aN = a * N
    V = 2 * aN
    total = 0
    sources = [i * N for i in range(a)] + [aN + j * N for j in range(a)]
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < aN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in out[i]:
                        v = aN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - aN, N)
                    row = T[y]
                    for i, h in inn[j]:
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


def _lift_anneal(a, N, d, D, T, invs, rng, iters, deadline):
    """Anneal voltages on a random d-regular bipartite base multigraph to zero the cost."""
    A_list = [i for i in range(a) for _ in range(d)]
    B_list = A_list[:]
    rng.shuffle(B_list)
    pairs = list(zip(A_list, B_list))
    groups = {}
    for k, (i, j) in enumerate(pairs):
        groups.setdefault((i, j), []).append(k)
    dart_g = [0] * len(pairs)
    for ks in groups.values():
        if len(ks) > N:
            return None
        for k, g in zip(ks, rng.sample(range(N), len(ks))):
            dart_g[k] = g
    darts = [(i, j, dart_g[k]) for k, (i, j) in enumerate(pairs)]
    cur = _lift_cost(a, N, darts, T, invs, D)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        k = rng.randrange(len(pairs))
        i, j, g_old = darts[k]
        used = {darts[t][2] for t in groups[(i, j)] if t != k}
        choices = [g for g in range(N) if g not in used and g != g_old]
        if not choices:
            continue
        darts[k] = (i, j, rng.choice(choices))
        v = _lift_cost(a, N, darts, T, invs, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[k] = (i, j, g_old)
    if cur == 0:
        return darts
    return None


def _lift_attempt(a, N, d, D, rng, deadline):
    """Try groups of order N for a lift with a base vertices per side."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        darts = _lift_anneal(a, N, d, D, T, invs, rng, LIFT_ITERS, deadline)
        if darts is not None:
            return T, darts
    return None


def _lift_graph(a, N, darts, T):
    """Expand a voltage assignment into (n, edges)."""
    aN = a * N
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, aN + j * N + T[x][g]))
    return 2 * aN, edges


def _lift_candidates(L, d, moore):
    """(n, a, N) with n >= L and n <= moore, sorted by n, a few N per base size a."""
    cands = []
    for a in range(1, LIFT_MAX_A + 1):
        lo = max(-(-L // (2 * a)), d + 1)
        for N in range(lo, lo + 3):
            n = 2 * a * N
            if n > moore or N > LIFT_MAX_N:
                break
            cands.append((n, a, N))
    cands.sort()
    return cands


# ----------------------------------------------------------------------------
# Old bi-Cayley annealing (kept as a fallback family).
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

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.8 * time_limit
    deadline = start + total
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

    # Phase 1: general voltage lifts (new construction), aiming above the current best.
    lift_deadline = start + 0.7 * total
    budget = 0.5
    while time.monotonic() < lift_deadline:
        cands = _lift_candidates(best_n + 1, d, moore)
        if not cands:
            break
        success = False
        for n, a, N in cands:
            now = time.monotonic()
            if now >= lift_deadline:
                break
            res = _lift_attempt(a, N, d, D, rng, min(lift_deadline, now + budget))
            if res is not None:
                T, darts = res
                consider(*_lift_graph(a, N, darts, T))
                success = True
                break
        if not success:
            budget *= 2

    # Phase 2: fallback bi-Cayley search over semidirect products (safe baseline).
    Nmax = moore // 2
    top = min(Nmax, Nmax // 2 + 6)
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
