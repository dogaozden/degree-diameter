import math
import random
import time

import lib

WINDOW0 = 12          # initial width of the target-size window above the current best
BUDGET_START = 1.0    # seconds per (a, N) attempt in the first pass
BUDGET_CAP = 6.0      # cap on per-attempt seconds as passes fail
MAX_GROUPS = 8        # groups tried per (a, N) attempt
MAX_BASE = 5          # base graphs with up to this many vertices per side
ITERS = 4000          # annealing steps per (group, base) try
T_HOT = 2.0           # initial annealing temperature (unreached-pair units)
T_COLD = 0.1          # final annealing temperature


# ----------------------------------------------------------------------------
# Fallback families (small, always validated before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Voltage lifts of small bipartite base multigraphs over non-cyclic groups.
#
# Base: a A-vertices and a B-vertices, each of degree d, built as the sum of d
# random permutation matrices (so the base is exactly d-regular, parallel darts
# allowed). Each dart (u, v, g) becomes the lift edges (u,x) -- (v, x*g) for all
# x in G. Lift order is 2*a*|G|.
#
# Left multiplication by h is an automorphism, so the diameter is decided by
# BFS from the 2a identity vertices (u,1). Annealing minimises the number of
# (source, vertex) pairs not reached within distance D.
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


def _table(N, m, k, r):
    """Multiplication table and inverse list for the group Z_m x|_r Z_k."""
    _, mul, inv = lib.semidirect_group(m, k, r)
    mt = [[mul(x, g) for g in range(N)] for x in range(N)]
    ginv = [inv(g) for g in range(N)]
    return mt, ginv


def _cells(a, d, rng):
    """d random permutations of range(a) -> list of d*a base darts (u, v) with row/col sums d."""
    cells = []
    for _ in range(d):
        p = list(range(a))
        rng.shuffle(p)
        for u in range(a):
            cells.append((u, p[u]))
    return cells


def _init_darts(cells, N, rng):
    """Assign voltages; parallel darts in the same cell get distinct group elements."""
    used = {}
    darts = []
    for u, v in cells:
        vals = used.setdefault((u, v), [])
        g = rng.randrange(N)
        while g in vals:
            g = rng.randrange(N)
        vals.append(g)
        darts.append([u, v, g])
    return darts


def _cost(a, N, darts, mt, D):
    """Total number of (source, vertex) pairs at distance > D over the 2a base identity sources."""
    aN = a * N
    adj = [[] for _ in range(2 * aN)]
    for u, v, g in darts:
        ba = u * N
        bb = aN + v * N
        for x in range(N):
            y = mt[x][g]
            adj[ba + x].append(bb + y)
            adj[bb + y].append(ba + x)
    total_v = 2 * aN
    unreached = 0
    sources = [u * N for u in range(a)] + [aN + v * N for v in range(a)]
    for s in sources:
        seen = bytearray(total_v)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for w in frontier:
                for z in adj[w]:
                    if not seen[z]:
                        seen[z] = 1
                        nxt.append(z)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        unreached += total_v - cnt
    return unreached


def _anneal(a, N, d, cells, mt, rng, D, deadline):
    """Anneal voltages to zero unreached pairs. Returns the dart list or None."""
    darts = _init_darts(cells, N, rng)
    cur = _cost(a, N, darts, mt, D)
    nd = len(darts)
    for it in range(ITERS):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        i = rng.randrange(nd)
        u, v, g = darts[i]
        others = [darts[j][2] for j in range(nd) if j != i and darts[j][0] == u and darts[j][1] == v]
        c = rng.randrange(N)
        if c in others:
            continue
        darts[i][2] = c
        val = _cost(a, N, darts, mt, D)
        if val <= cur or rng.random() < math.exp(-(val - cur) / temp):
            cur = val
        else:
            darts[i][2] = g
    if cur == 0:
        return darts
    return None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N with an a-vertex base until one lift has diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        mt, _ = _table(N, m, k, r)
        cells = _cells(a, d, rng)
        darts = _anneal(a, N, d, cells, mt, rng, D, deadline)
        if darts is not None:
            return mt, darts
    return None


def _edges(a, N, darts, mt):
    """Edge list of the lift; vertices (u, x) -> u*N + x, (v, y) -> a*N + v*N + y."""
    aN = a * N
    E = []
    for u, v, g in darts:
        for x in range(N):
            E.append((u * N + x, aN + v * N + mt[x][g]))
    return 2 * aN, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Record-matching case for D = 3: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    moore = lib.moore_bound(d, D)
    win = WINDOW0
    budget = BUDGET_START

    while time.monotonic() < deadline:
        lo = best[0]
        cands = []
        for a in range(1, MAX_BASE + 1):
            for N in range(d, moore // (2 * a) + 1):
                T = 2 * a * N
                if lo < T <= min(moore, lo + win):
                    cands.append((a, N))
        if not cands:
            if lo + win >= moore:
                break
            win *= 2
            continue
        rng.shuffle(cands)
        success = False
        for a, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(a, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            mt, darts = res
            n, e = _edges(a, N, darts, mt)
            consider(n, e)
            success = True
            break
        if not success:
            if budget < BUDGET_CAP:
                budget = min(BUDGET_CAP, budget * 1.5)
            else:
                win += WINDOW0

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
