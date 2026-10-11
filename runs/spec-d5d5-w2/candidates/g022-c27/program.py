import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per (p, N) attempt
ITERS = 800                   # annealing steps per (group, dart assignment) try
T_HOT = 6.0                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.3                  # final annealing temperature
BUDGET_START = 0.5            # seconds per attempt at the start
BUDGET_CAP = 4.0              # cap on per-attempt seconds
SPAN_START = 8                # initial width of the N window below the top
P_WEIGHTS = {1: 0.25, 2: 0.5, 3: 0.25}   # number of orbits per side


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
# Multi-orbit group lifts.
#
# Group G of order N (semidirect Z_m x| Z_k). The bipartite base has p "A"
# orbits and p "B" orbits. A dart (i, j, g) joins A_{i,x} to B_{j, x*g} for
# every x in G. A multiplicity matrix M[i][j] gives how many darts join A_i to
# B_j; row and column sums equal d, so the lift is d-regular. Each dart is a
# group element; darts inside one cell must use distinct elements so no edge
# repeats. Left multiplication by G is an automorphism that is transitive on
# each orbit, so distances from one source per orbit (2p sources) determine
# the diameter.
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


def _pattern(p, d, rng):
    """Random p x p nonnegative integer matrix with all row and column sums equal to d, or None."""
    for _ in range(300):
        M = [[0] * p for _ in range(p)]
        rows = [0] * p
        cols = [0] * p
        for _ in range(p * d):
            cand = [(i, j) for i in range(p) for j in range(p)
                    if rows[i] < d and cols[j] < d]
            if not cand:
                break
            i, j = rng.choice(cand)
            M[i][j] += 1
            rows[i] += 1
            cols[j] += 1
        if all(r == d for r in rows) and all(c == d for c in cols):
            return M
    return None


def _cost(p, N, T, invs, G, D):
    """Total (source, vertex) pairs at distance more than D, over one source per orbit."""
    pN = p * N
    size = 2 * pN
    adjA = [[] for _ in range(p)]
    adjB = [[] for _ in range(p)]
    for i in range(p):
        for j in range(p):
            for g in G[i][j]:
                adjA[i].append((j, g))
                adjB[j].append((i, invs[g]))
    total = 0
    for s in range(2 * p):
        src = s * N if s < p else pN + (s - p) * N
        seen = bytearray(size)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < pN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in adjA[i]:
                        v = pN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - pN, N)
                    row = T[y]
                    for i, h in adjB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += size - count
    return total


def _attempt(p, M, N, d, D, rng, deadline):
    """Anneal dart group elements over several groups of order N; return (n, edges) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    cells = [(i, j) for i in range(p) for j in range(p) if M[i][j] > 0]
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        G = [[(rng.sample(range(N), M[i][j]) if M[i][j] else []) for j in range(p)]
             for i in range(p)]
        cur = _cost(p, N, T, invs, G, D)
        for it in range(ITERS):
            if cur == 0 or time.monotonic() > deadline:
                break
            temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
            i, j = rng.choice(cells)
            idx = rng.randrange(len(G[i][j]))
            c = rng.randrange(N)
            if c in G[i][j]:
                continue
            old = G[i][j][idx]
            G[i][j][idx] = c
            v = _cost(p, N, T, invs, G, D)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                G[i][j][idx] = old
        if cur == 0:
            pN = p * N
            edges = []
            for i in range(p):
                for j in range(p):
                    for g in G[i][j]:
                        for x in range(N):
                            edges.append((i * N + x, pN + j * N + T[x][g]))
            return 2 * pN, edges
    return None


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

    side_max = lib._moore_bound(d, D) // 2   # vertices per side are at most this
    if side_max < 1:
        return best

    span = SPAN_START
    budget = BUDGET_START

    while time.monotonic() < deadline:
        # Orbit counts p whose window still allows a total beating best_n.
        cands = []
        for p in (1, 2, 3):
            hi = side_max // p
            lo = best_n // (2 * p) + 1
            if lo <= hi:
                cands.append((p, lo, hi))
        if not cands:
            break
        weights = [P_WEIGHTS[p] for p, _, _ in cands]
        p, lo, hi = rng.choices(cands, weights)[0]

        M = _pattern(p, d, rng)
        if M is None:
            continue
        a = max(lo, hi - span)
        N = rng.randint(a, hi)

        now = time.monotonic()
        att_deadline = min(deadline, now + budget)
        res = _attempt(p, M, N, d, D, rng, att_deadline)
        if res is not None:
            consider(*res)
        else:
            span = min(span + 2, hi)
            budget = min(BUDGET_CAP, budget * 1.2)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
