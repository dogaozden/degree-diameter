import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 8   # groups tried for one sampled (b, N) attempt
ITERS = 1500                 # annealing steps per (group, dart assignment) try
T_HOT = 1.5                  # initial annealing temperature (unreached-pair units)
T_COLD = 0.15                # final annealing temperature
SPREAD_START = 4             # initial width of the sampled order window above the best
SPREAD_CAP = 40
BUDGET_START = 1.0           # seconds per attempt, first attempts
BUDGET_CAP = 4.0
B_CHOICES = (1, 2, 2, 3, 3, 4)  # orbits per side; b >= 2 is the new multi-orbit family


# ----------------------------------------------------------------------------
# Baseline families (kept from the parent for the calibration and small cases).
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
# Multi-orbit voltage lifts over semidirect groups (new in this version).
#
# Base multigraph: b vertices A_0..A_{b-1} and b vertices B_0..B_{b-1}, each of
# degree d. A dart matrix M (b x b, row and column sums d) says how many darts
# join A_i to B_j. Each dart carries a group voltage g; for the group G of
# order N the lift has vertices A_{i,x} and B_{j,y} (x, y in G) and edges
# A_{i,x} -- B_{j,x*g} for every dart (i, j, g). Darts between the same (i, j)
# use distinct voltages, so the lift is simple and d-regular. Left
# multiplication is an automorphism, so the diameter is decided by BFS from the
# 2b sources A_{i,e} and B_{j,e}. The parent only uses b = 1 (bi-Cayley).
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _random_dart_matrix(b, d, rng):
    """b x b nonnegative integer matrix with all row and column sums d (sum of d random permutations)."""
    M = [[0] * b for _ in range(b)]
    for _ in range(d):
        p = list(range(b))
        rng.shuffle(p)
        for i in range(b):
            M[i][p[i]] += 1
    return M


def _unreached(b, N, T, invs, darts, D):
    """Total (source, vertex) pairs at distance > D, over the 2b orbit representatives."""
    bN = b * N
    V = 2 * bN
    out = [[] for _ in range(b)]
    inn = [[] for _ in range(b)]
    for i, j, g in darts:
        out[i].append((j, g))
        inn[j].append((i, invs[g]))
    sources = [i * N for i in range(b)] + [bN + j * N for j in range(b)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < bN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in out[i]:
                        v = bN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - bN, N)
                    row = T[y]
                    for i, h in inn[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(b, N, T, invs, M, d, D, rng, iters, deadline):
    """Anneal voltages (one per dart) to zero the unreached count. Returns darts or None."""
    darts = []
    for i in range(b):
        for j in range(b):
            if M[i][j]:
                for g in rng.sample(range(N), M[i][j]):
                    darts.append([i, j, g])
    if not darts:
        return None
    cur = _unreached(b, N, T, invs, darts, D)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        t = rng.randrange(len(darts))
        i, j, old = darts[t]
        c = rng.randrange(N)
        if c == old:
            continue
        if any(dd[0] == i and dd[1] == j and dd[2] == c for dd in darts):
            continue
        darts[t][2] = c
        v = _unreached(b, N, T, invs, darts, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / max(temp, 1e-9)):
            cur = v
        else:
            darts[t][2] = old
    if cur == 0:
        return darts
    return None


def _attempt(b, N, d, D, rng, deadline):
    """Try groups of order N with a random dart matrix until one lift has diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        M = _random_dart_matrix(b, d, rng)
        darts = _anneal(b, N, T, invs, M, d, D, rng, ITERS, deadline)
        if darts is not None:
            return darts, T
    return None


def _lift_edges(b, N, darts, T):
    """Edge list of the multi-orbit lift: A_{i,x} = i*N+x, B_{j,y} = b*N + j*N + y."""
    bN = b * N
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, bN + j * N + T[x][g]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.5
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

    # Record-matching case for D = 3: incidence graph of PG(2, d-1).
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
    spread = SPREAD_START
    budget = BUDGET_START

    while time.monotonic() < deadline:
        # Feasible (b, N) window: total vertices 2*b*N must beat best_n and stay <= Moore.
        options = []
        for b in set(B_CHOICES):
            lo = max(best_n // (2 * b) + 1, d)
            hi = min(moore // (2 * b), lo + spread)
            if lo <= hi:
                options.append((b, lo, hi))
        if not options:
            break
        b, lo, hi = rng.choice([o for o in options for _ in range(1 if o[0] != 1 else 1)])
        b, lo, hi = next((o for o in options if o[0] == b))
        N = rng.randint(lo, hi)

        now = time.monotonic()
        if now >= deadline:
            break
        att_deadline = min(deadline, now + budget)
        res = _attempt(b, N, d, D, rng, att_deadline)
        if res is None:
            budget = min(BUDGET_CAP, budget * 1.2)
            spread = min(SPREAD_CAP, spread + 1)
            continue
        darts, T = res
        consider(2 * b * N, _lift_edges(b, N, darts, T))
        spread = SPREAD_START

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
