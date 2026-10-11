import itertools
import math
import random
import time

import lib

ITERS = 700          # annealing steps per (group, base matrix) try
T_HOT = 4.0          # initial annealing temperature (unreached-pair units)
T_COLD = 0.2         # final annealing temperature
MAX_GROUPS = 10      # groups tried per attempt
BUDGET_START = 0.5   # seconds per candidate in the first pass
BUDGET_CAP = 4.0     # cap on per-candidate seconds as passes fail
WINDOW_FRAC = 0.95   # first search only V in [WINDOW_FRAC * top, top]
MAX_P = 3            # vertex orbits per side in the multi-orbit lift


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
# NEW IDEA: multi-orbit bi-Cayley lifts with a random regular base multigraph.
#
# A lift over a group G of order N with p vertex orbits on each side has
# vertices A_{i,x} and B_{j,y} (i, j < p, x, y in G), i.e. 2pN vertices.
# A "dart" (i, j, g) joins A_{i,x} to B_{j, x*g} for every x. Each A_i has
# out-degree d and each B_j in-degree d, so the base is a d-regular bipartite
# multigraph M on p + p vertices, with M[i][j] darts from A_i to B_j.
#
# Left multiplication by h is an automorphism, so one source per orbit
# (A_{i,e} and B_{j,e}) suffices to check the diameter. This extends the
# single-orbit bi-Cayley search of the parent to 2p orbits, which gives
# larger orders at the same degree.
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


def _base_matrix(p, d, rng):
    """Random d-regular bipartite base multiplicity matrix M (rows and columns sum to d)."""
    if p == 1:
        return [[d]]
    if p == 2:
        # Only [[a, d-a], [d-a, a]] is regular on 2+2 vertices; a = 0 or d disconnects.
        a = rng.randrange(1, d)
        return [[a, d - a], [d - a, a]]
    M = [[0] * p for _ in range(p)]
    perms = list(itertools.permutations(range(p)))
    for _ in range(d):
        s = rng.choice(perms)
        for i in range(p):
            M[i][s[i]] += 1
    return M


def _init_darts(p, M, N, rng):
    """Darts (i, j, g) with M[i][j] distinct group elements per pair, so the lift is simple."""
    darts = []
    for i in range(p):
        for j in range(p):
            for g in rng.sample(range(N), M[i][j]):
                darts.append((i, j, g))
    return darts


def _cost(N, p, T, invs, darts, D):
    """Count (source, vertex) pairs not within distance D, for one source per orbit."""
    outs = [[] for _ in range(p)]
    ins = [[] for _ in range(p)]
    for i, j, g in darts:
        outs[i].append((j, g))
        ins[j].append((i, invs[g]))  # B_{j,y} ~ A_{i, y*g^{-1}}
    V = 2 * p * N
    off = p * N
    sources = [i * N for i in range(p)] + [off + j * N for j in range(p)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < off:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in outs[i]:
                        v = off + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - off, N)
                    row = T[y]
                    for i, hinv in ins[j]:
                        v = i * N + row[hinv]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(N, p, T, invs, darts, D, rng, deadline):
    """Anneal the dart group elements to zero unreached pairs; return darts or None."""
    cur = _cost(N, p, T, invs, darts, D)
    for it in range(ITERS):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        t = rng.randrange(len(darts))
        i, j, _ = darts[t]
        c = rng.randrange(N)
        if any(a == i and b == j and h == c for a, b, h in darts):
            continue
        new = darts[:]
        new[t] = (i, j, c)
        v = _cost(N, p, T, invs, new, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = new, v
    return darts if cur == 0 else None


def _attempt(p, N, d, D, rng, deadline):
    """Try groups of order N with a random base matrix; return (order, mul, p, darts) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        M = _base_matrix(p, d, rng)
        darts = _init_darts(p, M, N, rng)
        res = _anneal(N, p, T, invs, darts, D, rng, deadline)
        if res is not None:
            return order, mul, p, res
    return None


def _edges(p, N, mul, darts):
    """Expand darts into the full lift with lib.group_lift (base vertices 0..p-1 | p..2p-1)."""
    return lib.group_lift(2 * p, [(i, p + j, g) for i, j, g in darts], N, mul)


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

    moore = lib.moore_bound(d, D)
    top = min(moore, moore // 2 + 12)

    # Candidate (V, p, N): V = 2pN vertices with N >= d+1 so darts fit in the group.
    cand_all = []
    for p in range(1, MAX_P + 1):
        for N in range(d + 1, top // (2 * p) + 1):
            cand_all.append((2 * p * N, p, N))
    if not cand_all:
        return best

    floor = int(WINDOW_FRAC * top)
    budget = BUDGET_START
    step = max(1, top // 50)

    while time.monotonic() < deadline:
        if best_n + 1 > top:
            break
        lo = max(best_n + 1, floor)
        cands = [c for c in cand_all if lo <= c[0] <= top]
        if not cands:
            if floor <= best_n + 1:
                break
            floor = max(best_n + 1, floor - step)
            continue
        rng.shuffle(cands)
        success = False
        for V, p, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(p, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            order, mul, pp, darts = res
            n, e = _edges(pp, order, mul, darts)
            consider(n, e)
            if best_n >= V:
                success = True
                break
        if not success:
            if budget < BUDGET_CAP:
                budget = min(BUDGET_CAP, budget * 1.5)
            elif floor > best_n + 1:
                floor = max(best_n + 1, floor - step)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
