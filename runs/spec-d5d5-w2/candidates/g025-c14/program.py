import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per (orbit count, N) attempt
ITERS = 600                   # annealing steps for single-orbit bi-Cayley tries
ORBIT_ITERS = 900             # annealing steps for multi-orbit tries
T_HOT = 1.5                   # initial annealing temperature (in unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
WINDOW_FRAC = 0.95            # search only N in [WINDOW_FRAC * top, top] first
BUDGET_START = 0.4            # seconds per single-orbit (N) attempt in the first pass
BUDGET_CAP = 3.0              # cap on single-orbit per-attempt seconds
ORBIT_BUDGET_START = 1.0      # seconds per multi-orbit (N) attempt in the first pass
ORBIT_BUDGET_CAP = 6.0        # cap on multi-orbit per-attempt seconds
# Time shares for the multi-orbit phase: (orbit count o, fraction of remaining time).
ORBIT_PLAN = [(1, 0.25), (2, 0.45), (3, 0.30)]


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
# Multi-orbit bi-Cayley lifts ("orbit patterns").
#
# New idea: instead of one orbit per side (a bi-Cayley graph), use o orbits
# A_0..A_{o-1} and B_0..B_{o-1}, each of size N over a group G of order N.
# A dart pattern c[i][j] (a nonnegative integer matrix with all row and column
# sums equal to d) says how many edges leave each A_i orbit into each B_j orbit.
# Such a pattern is sampled as a sum of d random permutation matrices, which
# guarantees the degree constraints. For each cell (i, j) we pick c[i][j]
# distinct group elements G[i][j], and join A_{i,x} to B_{j, x*g} for every
# g in G[i][j].
#
# Left multiplication by G is an automorphism, so the diameter is decided by
# eccentricities from the o + o orbit representatives A_{i,e} and B_{j,e}.
# The graph has 2*o*N vertices, and the search is annealing over the sets G[i][j]
# to remove unreached (source, vertex) pairs.
# ----------------------------------------------------------------------------

def _connected_pattern(c, o):
    """True if the bipartite pattern graph on the 2o orbits (edge where c[i][j] > 0) is connected."""
    seen = [False] * (2 * o)
    seen[0] = True
    stack = [0]
    while stack:
        u = stack.pop()
        if u < o:
            nb = [o + j for j in range(o) if c[u][j] > 0]
        else:
            j = u - o
            nb = [i for i in range(o) if c[i][j] > 0]
        for v in nb:
            if not seen[v]:
                seen[v] = True
                stack.append(v)
    return all(seen)


def _random_pattern(o, d, rng):
    """Sample a connected o x o pattern with all row and column sums d, as a sum of d permutations."""
    for _ in range(200):
        c = [[0] * o for _ in range(o)]
        for _ in range(d):
            p = list(range(o))
            rng.shuffle(p)
            for i in range(o):
                c[i][p[i]] += 1
        if _connected_pattern(c, o):
            return c
    return None


def _orbit_adj(N, o, T, G):
    """Adjacency lists of the multi-orbit graph. A_i vertices are i*N + x, B_j vertices are o*N + j*N + y."""
    n = 2 * o * N
    adj = [[] for _ in range(n)]
    for i in range(o):
        for j in range(o):
            base = o * N + j * N
            for g in G[i][j]:
                for x in range(N):
                    u = i * N + x
                    v = base + T[x][g]
                    adj[u].append(v)
                    adj[v].append(u)
    return adj


def _orbit_unreached(N, o, adj, D):
    """Count unreached (source, vertex) pairs over the 2o orbit representatives."""
    n = 2 * o * N
    sources = [i * N for i in range(o)] + [o * N + j * N for j in range(o)]
    total = 0
    for s in sources:
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += n - cnt
    return total


def _anneal_orbits(N, o, T, C, D, rng, iters, deadline):
    """Anneal the sets G[i][j] (sizes C[i][j]) until every orbit representative reaches all vertices within D."""
    G = [[(rng.sample(range(N), C[i][j]) if C[i][j] else []) for j in range(o)]
         for i in range(o)]
    cur = _orbit_unreached(N, o, _orbit_adj(N, o, T, G), D)
    cells = [(i, j) for i in range(o) for j in range(o) if C[i][j]]
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i, j = rng.choice(cells)
        t = rng.randrange(len(G[i][j]))
        c = rng.randrange(N)
        if c in G[i][j]:
            continue
        old = G[i][j][t]
        G[i][j][t] = c
        v = _orbit_unreached(N, o, _orbit_adj(N, o, T, G), D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            G[i][j][t] = old
    return G if cur == 0 else None


def _attempt_orbits(N, o, d, D, rng, deadline):
    """Try groups of order N with random patterns; return (n, edges) for a valid lift, or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        C = _random_pattern(o, d, rng)
        if C is None:
            continue
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        G = _anneal_orbits(N, o, T, C, D, rng, ORBIT_ITERS, deadline)
        if G is not None:
            edges = []
            for i in range(o):
                for j in range(o):
                    base = o * N + j * N
                    for g in G[i][j]:
                        for x in range(N):
                            edges.append((i * N + x, base + T[x][g]))
            return 2 * o * N, edges
    return None


def _search_orbits(o, d, D, rng, deadline, best_n):
    """Search multi-orbit lifts with o orbits per side, beating best_n; return (n, edges) or None."""
    top = lib._moore_bound(d, D) // (2 * o)
    lo_floor = max(d + 1, best_n // (2 * o) + 1)
    if lo_floor > top:
        return None
    floor = max(lo_floor, int(WINDOW_FRAC * top))
    bestN = lo_floor - 1
    budget = ORBIT_BUDGET_START
    found = None
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
            res = _attempt_orbits(N, o, d, D, rng, att_deadline)
            if res is None:
                continue
            n, edges = res
            if lib.is_valid(n, edges, d, D):
                found = (n, edges)
                bestN = N
                success = True
                break
        if not success:
            if budget < ORBIT_BUDGET_CAP:
                budget = min(ORBIT_BUDGET_CAP, budget * 1.5)
            elif floor > lo_floor:
                floor -= 1
    return found


# ----------------------------------------------------------------------------
# Single-orbit bi-Cayley search over semidirect products Z_m x| Z_k of order N.
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


def _search_single(d, D, rng, deadline, best_n):
    """Parent-style single-orbit bi-Cayley search; return (n, edges) or None."""
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + 6)
    if top < d + 1:
        return None
    floor = max(d + 1, int(WINDOW_FRAC * top))
    bestN = best_n // 2
    budget = BUDGET_START
    found = None
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
            n = 2 * N
            if lib.is_valid(n, edges, d, D):
                found = (n, edges)
                bestN = N
                success = True
                break
        if not success:
            if budget < BUDGET_CAP:
                budget = min(BUDGET_CAP, budget * 1.5)
            elif floor > d + 1:
                floor -= 1
    return found


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

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

    # Search phase: split the remaining time over orbit counts. Each segment's
    # deadline is absolute, so time a segment does not use flows to the next one.
    t_now = time.monotonic()
    avail = deadline - t_now
    if avail > 0:
        cum = 0.0
        for o, share in ORBIT_PLAN:
            seg_end = t_now + avail * (cum + share)
            cum += share
            if time.monotonic() >= seg_end:
                continue
            if o == 1:
                res = _search_single(d, D, rng, seg_end, best[0])
            else:
                res = _search_orbits(o, d, D, rng, seg_end, best[0])
            if res is not None:
                consider(*res)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
