import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per order within one attempt
ITERS = 600                   # annealing steps per (group, connection set) try
T_HOT = 1.5                   # initial annealing temperature (in unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
WINDOW_FRAC = 0.95            # search only N in [WINDOW_FRAC * top, top] first
BUDGET_START = 0.4            # seconds per (N) attempt in the first pass
BUDGET_CAP = 3.0              # cap on per-attempt seconds as passes fail

# Multi-orbit bi-Cayley lifts (new family): a A-orbits and a B-orbits over one group.
MULTI_ITERS = 900             # annealing steps per (group) try in a multi-orbit lift
MULTI_BUDGET_START = 1.0      # seconds per (a, N) attempt, first pass
MULTI_BUDGET_CAP = 4.0        # cap on per-attempt seconds for multi-orbit lifts
MULTI_MAX_A = 6               # largest number of orbits per side tried
MULTI_SPAN = 40               # candidate totals a*N from best_half+1 up to best_half+MULTI_SPAN
MULTI_FRAC = 0.7              # share of the search time given to multi-orbit lifts
DUP_PENALTY = 3               # cost per duplicate dart (same orbit pair and same label)


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
# Single-orbit bi-Cayley search over semidirect products Z_m x| Z_k of order N.
#
# Vertices A_x and B_y (x, y in G). Edge A_x -- B_{x s} for s in S, |S| = d.
# Left multiplication is an automorphism, so eccentricities from A_0 and B_0
# decide the diameter. Identity is WLOG in S.
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
# Multi-orbit bi-Cayley lifts (new family).
#
# Take a orbits on each side and a group G of order N. Vertices A_{i,x} and
# B_{j,y} for orbit indices i, j in 0..a-1 and x, y in G. The base graph is
# d-regular on a+a vertices, built as the union of d permutations
# perms[t] (dart t leaves A-orbit i for B-orbit perms[t][i]). Dart (i, t) carries
# a label g = L[i][t] in G, giving edges A_{i,x} -- B_{perms[t][i], x g}.
#
# Every A and B vertex has degree d (before duplicate removal). Left
# multiplication is an automorphism, so the diameter is decided by BFS from
# A_{i,e} and B_{j,e} for every orbit index. a = 1 reduces to the single-orbit
# search above, so a >= 2 is the new part.
# ----------------------------------------------------------------------------

def _multi_graph(a, N, d, perms, L, T):
    """Adjacency lists and the number of duplicate darts for a multi-orbit lift."""
    n = 2 * a * N
    adj = [[] for _ in range(n)]
    dups = 0
    for i in range(a):
        used = {}
        for t in range(d):
            j = perms[t][i]
            g = L[i][t]
            s = used.setdefault(j, set())
            if g in s:
                dups += 1
                continue
            s.add(g)
            off = a * N + j * N
            for x in range(N):
                u = i * N + x
                v = off + T[x][g]
                adj[u].append(v)
                adj[v].append(u)
    return adj, dups


def _multi_unreached(a, N, D, adj):
    """Count (source, vertex) pairs at distance > D, over one source per orbit on each side."""
    n = 2 * a * N
    sources = [i * N for i in range(a)] + [a * N + j * N for j in range(a)]
    total = 0
    for src in sources:
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


def _multi_cost(a, N, d, D, perms, L, T):
    adj, dups = _multi_graph(a, N, d, perms, L, T)
    return _multi_unreached(a, N, D, adj) + DUP_PENALTY * dups


def _anneal_multi(a, N, d, D, perms, T, rng, iters, deadline):
    """Anneal the dart labels L[i][t] until the lift has no duplicates and diameter <= D."""
    L = [[rng.randrange(N) for _ in range(d)] for _ in range(a)]
    cur = _multi_cost(a, N, d, D, perms, L, T)
    for it in range(iters):
        if cur == 0:
            return L
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(a)
        t = rng.randrange(d)
        old = L[i][t]
        new = rng.randrange(N)
        if new == old:
            continue
        L[i][t] = new
        v = _multi_cost(a, N, d, D, perms, L, T)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            L[i][t] = old
    if cur == 0:
        return L
    return None


def _multi_attempt(a, N, d, D, rng, deadline):
    """Try groups of order N for an a-orbit lift until one gives diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        perms = [rng.sample(range(a), a) for _ in range(d)]
        L = _anneal_multi(a, N, d, D, perms, T, rng, MULTI_ITERS, deadline)
        if L is not None:
            return perms, L, T
    return None


def _multi_edges(a, N, d, perms, L, T):
    """Explicit edge list of a multi-orbit lift (A ids 0..aN-1, B ids aN..2aN-1)."""
    edges = set()
    for i in range(a):
        for t in range(d):
            j = perms[t][i]
            g = L[i][t]
            off = a * N + j * N
            for x in range(N):
                edges.add((i * N + x, off + T[x][g]))
    return sorted(edges)


def _multi_cands(lo, hi, amax):
    """All (a, N) with a in 2..amax and lo <= a*N <= hi."""
    out = []
    for a in range(2, amax + 1):
        for N in range(max(2, -(-lo // a)), hi // a + 1):
            out.append((a, N))
    return out


def _multi_phase(d, D, rng, best_n, phase_deadline, consider, Nmax):
    """Search multi-orbit lifts with total orbit count a*N just above the current best half."""
    best_half = best_n // 2
    budget = MULTI_BUDGET_START
    while time.monotonic() < phase_deadline:
        hi = min(Nmax, best_half + MULTI_SPAN)
        cands = _multi_cands(best_half + 1, hi, MULTI_MAX_A)
        if not cands:
            break
        rng.shuffle(cands)
        success = False
        for a, N in cands:
            now = time.monotonic()
            if now >= phase_deadline:
                break
            res = _multi_attempt(a, N, d, D, rng, min(phase_deadline, now + budget))
            if res is None:
                continue
            perms, L, T = res
            consider(2 * a * N, _multi_edges(a, N, d, perms, L, T))
            best_half = max(best_half, a * N)
            success = True
            break
        if not success:
            budget = min(MULTI_BUDGET_CAP, budget * 1.5)


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

    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley-type graph has 2*(a*N) vertices

    # Phase 1: multi-orbit lifts (a >= 2), the new family.
    now = time.monotonic()
    if now < deadline and Nmax >= 3:
        phase_deadline = now + MULTI_FRAC * (deadline - now)
        _multi_phase(d, D, rng, best_n, phase_deadline, consider, Nmax)

    # Phase 2: single-orbit bi-Cayley search near the Moore bound.
    top = min(Nmax, Nmax // 2 + 6)
    if top < d + 1:
        if not lib.is_valid(best[0], best[1], d, D):
            return 1, []
        return best

    floor = max(d + 1, int(WINDOW_FRAC * top))
    bestN = best_n // 2
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
