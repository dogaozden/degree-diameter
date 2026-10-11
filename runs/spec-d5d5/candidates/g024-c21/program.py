import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# Search parameters
# ----------------------------------------------------------------------------
MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per (b, N) attempt
ITERS = 600                   # annealing steps per (group, base graph) try
T_HOT = 1.2                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.1                  # final annealing temperature
BASE_SIZES = (1, 2, 3, 4)     # b = number of A-orbits = number of B-orbits
MAX_BUDGET = 20.0             # cap on per-(b) attempt time, seconds


# ----------------------------------------------------------------------------
# Baseline families (fast, always checked with lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    import itertools
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
# NEW IDEA: multi-orbit (b-orbit) group lifts searched by annealing.
#
# The parent only searches single-orbit bi-Cayley graphs (b = 1). Here the
# base graph has b vertices on each side. Group G of order N acts by left
# multiplication, and the lift has vertices A(i, x) and B(j, y) for
# i, j in 0..b-1 and x, y in G. A "dart" (i, j, g) joins A(i, x) to
# B(j, x g) for every x.
#
# Each A-orbit i gets exactly d darts, and each B-orbit j receives exactly d
# darts, so the lift is d-regular on both sides before deduplication and
# bipartite by construction. Left multiplication is an automorphism, so the
# diameter condition only needs BFS from one representative per orbit:
# A(i, e) and B(j, e). That gives 2b sources in total.
#
# Moves: change the group label g of one dart, or swap the target orbit j of
# two darts (this keeps every B-orbit at in-degree d). Cost = number of
# unreached (source, vertex) pairs. This generalises the parent's search
# (b = 1) and tends to find larger orders when b >= 2.
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


def _init_darts(b, d, N, rng):
    """Random dart list [i, j, g] with each A-orbit used d times and each B-orbit d times, all triples distinct."""
    A = [i for i in range(b) for _ in range(d)]
    B = [j for j in range(b) for _ in range(d)]
    rng.shuffle(B)
    darts = []
    seen = set()
    for k in range(len(A)):
        i, j = A[k], B[k]
        g = rng.randrange(N)
        while (i, j, g) in seen:
            g = rng.randrange(N)
        seen.add((i, j, g))
        darts.append([i, j, g])
    return darts


def _unreached(b, N, T, invs, darts, D):
    """Count (source, vertex) pairs at distance > D, over the 2b orbit representatives."""
    outs = [[] for _ in range(b)]
    ins = [[] for _ in range(b)]
    for i, j, g in darts:
        outs[i].append((j, g))
        ins[j].append((i, invs[g]))
    BN = b * N
    V = 2 * BN
    total = 0
    sources = [i * N for i in range(b)] + [BN + j * N for j in range(b)]
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < BN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in outs[i]:
                        v = BN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - BN, N)
                    row = T[y]
                    for i, gi in ins[j]:
                        v = i * N + row[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(b, N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over dart lists to drive unreached pairs to zero."""
    darts = _init_darts(b, d, N, rng)
    cur = _unreached(b, N, T, invs, darts, D)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        cand = [row[:] for row in darts]
        if b == 1 or rng.random() < 0.7:
            k = rng.randrange(len(cand))
            cand[k][2] = rng.randrange(N)
        else:
            k1 = rng.randrange(len(cand))
            k2 = rng.randrange(len(cand))
            if cand[k1][1] == cand[k2][1]:
                continue
            cand[k1][1], cand[k2][1] = cand[k2][1], cand[k1][1]
        if len(set(tuple(r) for r in cand)) != len(cand):
            continue
        v = _unreached(b, N, T, invs, cand, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = cand, v
    return darts if cur == 0 else None


def _attempt(b, N, d, D, rng, deadline):
    """Try groups of order N with b base orbits; return (T, darts) on success, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        darts = _anneal(b, N, T, invs, d, D, rng, ITERS, deadline)
        if darts is not None:
            return T, darts
    return None


def _lift(b, N, T, darts):
    """Build the lift: A(i, x) = i*N + x, B(j, y) = b*N + j*N + y."""
    BN = b * N
    edges = set()
    for i, j, g in darts:
        for x in range(N):
            edges.add((i * N + x, BN + j * N + T[x][g]))
    return 2 * BN, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5 * time_limit, min(0.85 * time_limit, time_limit - 6.0))
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

    Mb = lib._moore_bound(d, D)
    bs = []
    Nmax = {}
    for b in BASE_SIZES:
        nm = Mb // (2 * b)          # 2*b*N <= Moore bound
        if nm >= max(d, 2):
            bs.append(b)
            Nmax[b] = nm

    targ = {}
    budget = {b: 2.0 for b in bs}

    while bs and time.monotonic() < deadline:
        for b in list(bs):
            now = time.monotonic()
            if now >= deadline:
                break
            lo = best_n // (2 * b) + 1          # need 2*b*N > best_n
            N = max(targ.get(b, lo), lo, d)
            if N > Nmax[b]:
                bs.remove(b)
                continue
            targ[b] = N
            att_deadline = min(deadline, now + budget[b])
            res = _attempt(b, N, d, D, rng, att_deadline)
            if res is None:
                budget[b] = min(budget[b] * 1.5, MAX_BUDGET)
            else:
                T, darts = res
                n, e = _lift(b, N, T, darts)
                consider(n, e)
                targ[b] = N + 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
