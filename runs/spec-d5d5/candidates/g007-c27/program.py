import itertools
import math
import random
import time

import lib

ITERS = 1500                  # annealing steps per (group, base-graph) try
T_HOT = 2.0                   # starting temperature (unreached-pair units)
T_COLD = 0.1                  # final temperature
MAX_GROUPS = 6                # groups tried per (order, t) attempt
MAX_BASE = 4                  # maximum base vertices per side in a lift
CAND_PER_PASS = 8             # candidate orders attempted per pass


# ----------------------------------------------------------------------------
# Baseline families (always validated before use).
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
    """W(q) for the largest small prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bipartite group lifts with t base vertices per side.
#
# Group G of order N (semidirect Z_m x| Z_k, element 0 = identity).
# Vertices A(i, x) and B(j, y), i, j in 0..t-1, x, y in G.
# Each "dart" (i, j, g) gives edges A(i, x) -- B(j, x*g) for all x.
# Every A-vertex class gets exactly d darts, every B-class gets exactly d darts,
# so the graph is d-regular and bipartite. Darts are triples with no repeats.
# Left multiplication by G is an automorphism, so BFS from A(i, e) and B(j, e)
# for each class decides the diameter. This is a different construction family
# from the plain bi-Cayley search: it lets t > 1 base vertices per side.
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


def _cost(N, t, D, mul_t, inv_t, darts):
    """Count (source, vertex) pairs not within distance D, over one source per base class."""
    tN = t * N
    n = 2 * tN
    adjA = [[] for _ in range(t)]
    adjB = [[] for _ in range(t)]
    for i, j, g in darts:
        adjA[i].append((j, g))
        adjB[j].append((i, inv_t[g]))
    sources = [i * N for i in range(t)] + [tN + j * N for j in range(t)]
    total = 0
    for s in sources:
        seen = bytearray(n)
        seen[s] = 1
        count = 1
        frontier = [s]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < tN:
                    i, x = divmod(u, N)
                    row = mul_t[x]
                    for j, g in adjA[i]:
                        v = tN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - tN, N)
                    row = mul_t[y]
                    for i, gi in adjB[j]:
                        v = i * N + row[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += n - count
    return total


def _dup_free(t, d, slots_j, gs):
    """True if all darts (slot // d, slots_j[slot], gs[slot]) are distinct."""
    seen = set()
    for k in range(t * d):
        key = (k // d, slots_j[k], gs[k])
        if key in seen:
            return False
        seen.add(key)
    return True


def _anneal(N, t, d, D, mul_t, inv_t, rng, deadline):
    """Anneal the dart assignment to zero unreached pairs; return darts list or None."""
    slots = t * d
    slots_j = [j for j in range(t) for _ in range(d)]
    gs = [0] * slots
    for _ in range(200):
        rng.shuffle(slots_j)
        gs = [rng.randrange(N) for _ in range(slots)]
        if _dup_free(t, d, slots_j, gs):
            break
    else:
        return None

    def darts_of(sj, g):
        return [(k // d, sj[k], g[k]) for k in range(slots)]

    cur = _cost(N, t, D, mul_t, inv_t, darts_of(slots_j, gs))
    for it in range(ITERS):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        new_j = slots_j[:]
        new_g = gs[:]
        if rng.random() < 0.5:
            k = rng.randrange(slots)
            new_g[k] = rng.randrange(N)
        else:
            k1 = rng.randrange(slots)
            k2 = rng.randrange(slots)
            new_j[k1], new_j[k2] = new_j[k2], new_j[k1]
        if not _dup_free(t, d, new_j, new_g):
            continue
        v = _cost(N, t, D, mul_t, inv_t, darts_of(new_j, new_g))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            slots_j, gs, cur = new_j, new_g, v
    if cur == 0:
        return darts_of(slots_j, gs)
    return None


def _attempt(N, t, d, D, rng, deadline):
    """Try groups of order N for a t-base lift; return (darts, mul_t) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        mul_t = [[mul(x, g) for g in range(N)] for x in range(N)]
        inv_t = [inv(g) for g in range(N)]
        darts = _anneal(N, t, d, D, mul_t, inv_t, rng, deadline)
        if darts is not None:
            return darts, mul_t
    return None


def _lift_edges(N, t, darts, mul_t):
    """Expand darts into the explicit edge list of the lift."""
    tN = t * N
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, tN + j * N + mul_t[x][g]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
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

    # Record-matching case for D = 3.
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

    # Search: bipartite t-base group lifts with n = 2*t*N, ascending from a high floor.
    Vmax = lib._moore_bound(d, D)
    lo_cur = max(best_n + 1, Vmax // 2)
    budget = 0.4
    while time.monotonic() < deadline:
        cands = []
        for V in range(max(lo_cur, best_n + 1), Vmax + 1):
            for t in range(1, MAX_BASE + 1):
                if V % (2 * t):
                    continue
                N = V // (2 * t)
                if N <= d:
                    continue
                cands.append((V, t, N))
            if len(cands) >= CAND_PER_PASS:
                break
        if not cands:
            if lo_cur <= best_n + 1:
                break
            lo_cur = max(best_n + 1, lo_cur - max(1, Vmax // 10))
            continue

        success = False
        for V, t, N in cands[:CAND_PER_PASS]:
            if V <= best_n:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(N, t, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            darts, mul_t = res
            consider(2 * t * N, _lift_edges(N, t, darts, mul_t))
            success = True

        if not success:
            if budget < 4.0:
                budget *= 2
            else:
                budget = 0.4
                lo_cur = max(best_n + 1, lo_cur - max(1, Vmax // 20))

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
