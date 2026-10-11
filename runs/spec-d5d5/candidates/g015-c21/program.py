import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families (cheap, always checked with lib.is_valid).
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
# NEW: multi-orbit group voltage lift (t A-orbits, t B-orbits, group of order N).
#
# Vertices: A_{i,x} = i*N + x and B_{j,y} = (t+j)*N + y, for x, y in G.
# The base graph is d-regular bipartite on t + t vertices, given by d layers.
# Layer l joins A_i to B_{perm_l(i)} with voltage volt_l(i):
#     A_{i,x} -- B_{j, x*g}.
# Left multiplication by G is an automorphism, so the diameter test only needs
# BFS from the t + t orbit representatives (identity of each orbit).
# t = 1 is the ordinary bi-Cayley search, so this family contains the parent's.
# Vertex count is 2tN, which lets us aim above 336 with different (t, N) pairs.
# ----------------------------------------------------------------------------

MAX_GROUPS = 6     # groups tried for one (t, N) attempt
TEMP = 0.5         # annealing temperature for integer unreached-pair costs
TMAX = 6           # largest number of orbits per side


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


def _build_adj(t, N, d, T, invs, perms, volts):
    """Adjacency lists (with possible duplicates) of the multi-orbit lift."""
    adjA = [[] for _ in range(t)]   # adjA[i] = [(j, g)] darts leaving A_i
    adjB = [[] for _ in range(t)]   # adjB[j] = [(i, g)] darts entering B_j
    for l in range(d):
        pl = perms[l]
        vl = volts[l]
        for i in range(t):
            j = pl[i]
            g = vl[i]
            adjA[i].append((j, g))
            adjB[j].append((i, g))
    n = 2 * t * N
    nb = [None] * n
    for i in range(t):
        base = i * N
        darts = adjA[i]
        for x in range(N):
            Tx = T[x]
            nb[base + x] = [(t + j) * N + Tx[g] for j, g in darts]
    for j in range(t):
        base = (t + j) * N
        darts = adjB[j]
        for y in range(N):
            Ty = T[y]
            nb[base + y] = [i * N + Ty[invs[g]] for i, g in darts]
    return n, nb


def _cost(t, N, d, D, T, invs, perms, volts):
    """Total number of (representative, vertex) pairs at distance > D."""
    n, nb = _build_adj(t, N, d, T, invs, perms, volts)
    sources = [i * N for i in range(t)] + [(t + j) * N for j in range(t)]
    total = 0
    for s in sources:
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in nb[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += n - count
    return total


def _anneal(t, N, d, D, T, invs, rng, deadline):
    """Anneal layer permutations and voltages until every representative reaches all within D."""
    perms = []
    volts = []
    for _ in range(d):
        p = list(range(t))
        rng.shuffle(p)
        perms.append(p)
        volts.append([rng.randrange(N) for _ in range(t)])
    cur = _cost(t, N, d, D, T, invs, perms, volts)
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        l = rng.randrange(d)
        if t >= 2 and rng.random() < 0.3:
            # Swap two targets within one layer (keeps each layer a permutation).
            i, i2 = rng.sample(range(t), 2)
            p = perms[l]
            p[i], p[i2] = p[i2], p[i]
            c = _cost(t, N, d, D, T, invs, perms, volts)
            if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP):
                cur = c
            else:
                p[i], p[i2] = p[i2], p[i]
        else:
            if N == 1:
                continue
            i = rng.randrange(t)
            old = volts[l][i]
            new = rng.randrange(N)
            if new == old:
                continue
            volts[l][i] = new
            c = _cost(t, N, d, D, T, invs, perms, volts)
            if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP):
                cur = c
            else:
                volts[l][i] = old
    return perms, volts


def _attempt(t, N, d, D, rng, deadline):
    """Try up to MAX_GROUPS groups of order N for the (t, N) lift."""
    groups = _groups(N)
    rng.shuffle(groups)
    groups = groups[:MAX_GROUPS]
    if not groups:
        return None
    slice_ = max(0.05, (deadline - time.monotonic()) / len(groups))
    for m, k, r in groups:
        now = time.monotonic()
        if now >= deadline:
            break
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        res = _anneal(t, N, d, D, T, invs, rng, min(deadline, now + slice_))
        if res is not None:
            perms, volts = res
            return T, perms, volts
    return None


def _lift_edges(t, N, d, T, perms, volts):
    """Edge list of the lift found by _attempt."""
    es = set()
    for l in range(d):
        for i in range(t):
            j = perms[l][i]
            g = volts[l][i]
            for x in range(N):
                es.add((i * N + x, (t + j) * N + T[x][g]))
    return sorted(es)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Calibration-type shortcut: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D == 1:
        consider(2, [(0, 1)])
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
    budget = 1.0
    fails = 0
    while time.monotonic() < deadline:
        best_n = best[0]
        # Orbit counts t whose order range can still beat the current best.
        valid_ts = [t for t in range(1, TMAX + 1)
                    if best_n // (2 * t) + 1 <= moore // (2 * t)]
        if not valid_ts:
            break
        t = rng.choice(valid_ts)
        Nlow = best_n // (2 * t) + 1
        Nhigh = moore // (2 * t)
        N = Nlow + min(int(rng.expovariate(0.7)), Nhigh - Nlow)

        att_deadline = min(deadline, time.monotonic() + budget)
        res = _attempt(t, N, d, D, rng, att_deadline)
        if res is None:
            fails += 1
            budget = min(1.0 + 0.1 * fails, 5.0)
            continue
        T, perms, volts = res
        edges = _lift_edges(t, N, d, T, perms, volts)
        consider(2 * t * N, edges)
        fails = 0
        budget = 1.0

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
