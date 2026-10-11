import itertools
import math
import random
import time

import lib

ITERS = 500                   # annealing steps per (group, voltage) try
T_HOT = 2.0                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
MAX_GROUPS = 6                # groups tried per (k, M) attempt
MAX_K = 3                     # base vertices per side in the multi-orbit bi-lift
POOL_WINDOW = 48              # only totals this far above the current best are tried
MIN_BUDGET = 0.6              # seconds for the first attempt on each candidate


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
# Groups: semidirect products Z_m x|_r Z_k of a given order M.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for kk in range(1, N + 1):
        if N % kk:
            continue
        m = N // kk
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                out.append((m, kk, r))
    return out


# ----------------------------------------------------------------------------
# NEW: multi-orbit bi-lift search.
#
# The parent only uses one vertex per side of a base graph (a bi-Cayley graph).
# Here the base graph has k vertices A_0..A_{k-1} and B_0..B_{k-1}, and the
# lift group G has order M, so the graph has 2*k*M vertices. The base is d
# "layers", each a permutation sigma_t of range(k) with voltages g_{t,i}, and
#
#     A_{i,x}  ~  B_{sigma_t(i), x * g_{t,i}}     for each layer t.
#
# Each A_i has d distinct neighbour pairs (requirement: no duplicate edges).
# Each B_j receives exactly one dart per layer, so every degree equals d.
# Left multiplication by G is an automorphism that is transitive on each fibre,
# so diameter <= D holds iff the 2k fibre-representatives A_{i,e}, B_{j,e}
# reach everything within D steps. Annealing over voltages and layer
# permutations drives the count of unreached pairs to zero.
# ----------------------------------------------------------------------------

def _pairs_ok(k, d, perm, volt):
    """True if for each base vertex i the d darts (sigma_t(i), g_{t,i}) are pairwise distinct."""
    for i in range(k):
        seen = set()
        for t in range(d):
            seen.add((perm[t][i], volt[t][i]))
        if len(seen) < d:
            return False
    return True


def _cost(k, M, d, D, perm, volt, MT, INV):
    """Total unreached (source, vertex) pairs over the 2k fibre representatives."""
    KM = k * M
    n = 2 * KM
    aout = [[(perm[t][i], volt[t][i]) for t in range(d)] for i in range(k)]
    bin_ = [[] for _ in range(k)]
    for t in range(d):
        for i in range(k):
            bin_[perm[t][i]].append((i, INV[volt[t][i]]))
    sources = [i * M for i in range(k)] + [KM + j * M for j in range(k)]
    total = 0
    for s in sources:
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < KM:
                    i, x = divmod(u, M)
                    row = MT[x]
                    for j, g in aout[i]:
                        v = KM + j * M + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - KM, M)
                    row = MT[y]
                    for i, gi in bin_[j]:
                        v = i * M + row[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += n - count
    return total


def _anneal(k, M, d, D, MT, INV, rng, iters, deadline):
    """Simulated annealing over layer permutations and voltages; returns (perm, volt) or None."""
    perm = volt = None
    ok_init = False
    for _ in range(50):
        perm = [rng.sample(range(k), k) for _ in range(d)]
        volt = [[rng.randrange(M) for _ in range(k)] for _ in range(d)]
        for _ in range(200):
            if _pairs_ok(k, d, perm, volt):
                break
            t = rng.randrange(d)
            i = rng.randrange(k)
            volt[t][i] = rng.randrange(M)
        if _pairs_ok(k, d, perm, volt):
            ok_init = True
            break
    if not ok_init:
        return None

    cur = _cost(k, M, d, D, perm, volt, MT, INV)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        t = rng.randrange(d)
        i = rng.randrange(k)
        if k == 1 or rng.random() < 0.7:
            old = volt[t][i]
            new = rng.randrange(M)
            if new == old:
                continue
            volt[t][i] = new
            if not _pairs_ok(k, d, perm, volt):
                volt[t][i] = old
                continue
            v = _cost(k, M, d, D, perm, volt, MT, INV)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                volt[t][i] = old
        else:
            old = perm[t][:]
            perm[t] = rng.sample(range(k), k)
            if not _pairs_ok(k, d, perm, volt):
                perm[t] = old
                continue
            v = _cost(k, M, d, D, perm, volt, MT, INV)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                perm[t] = old
    if cur == 0:
        return perm, volt
    return None


def _attempt(k, M, d, D, rng, deadline):
    """Try groups of order M for the k-vertex bi-lift; return (perm, volt, MT) or None."""
    groups = _groups(M)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, kk, r)
        MT = [[mul(x, g) for g in range(M)] for x in range(M)]
        INV = [inv(g) for g in range(M)]
        res = _anneal(k, M, d, D, MT, INV, rng, ITERS, deadline)
        if res is not None:
            perm, volt = res
            return perm, volt, MT
    return None


def _edges(k, M, d, MT, perm, volt):
    """Explicit (n, edges) of the lift: A vertices 0..kM-1, B vertices kM..2kM-1."""
    KM = k * M
    edges = []
    for t in range(d):
        for i in range(k):
            j = perm[t][i]
            g = volt[t][i]
            for x in range(M):
                edges.append((i * M + x, KM + j * M + MT[x][g]))
    return 2 * KM, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    moore = lib._moore_bound(d, D)
    # Candidate (total, k, M) with total = 2*k*M just above the current best.
    def make_pool():
        pool = []
        hi = min(moore, best_n + POOL_WINDOW)
        for k in range(1, MAX_K + 1):
            for M in range(d, hi // (2 * k) + 1):
                T = 2 * k * M
                if best_n < T <= hi:
                    pool.append((T, k, M))
        pool.sort()
        return pool

    pool = make_pool()
    budget = MIN_BUDGET
    while time.monotonic() < deadline and pool:
        for T, k, M in pool:
            if T <= best_n:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(k, M, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            perm, volt, MT = res
            n, e = _edges(k, M, d, MT, perm, volt)
            consider(n, e)
        pool = [p for p in make_pool() if p[0] > best_n] if best_n > 1 else pool
        budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
