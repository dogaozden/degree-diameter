import itertools
import math
import random
import time

import lib

ITERS = 2500            # annealing steps per (group, base-graph) try
T_HOT = 2.0             # initial temperature (unreached-pair units)
T_COLD = 0.2            # final temperature
MAX_GROUPS = 8          # groups tried per attempt
GROUP_MOVE = 0.4        # chance a voltage move proposes a product of two voltages
SWAP_MOVE = 0.3         # chance a move swaps two targets in one base permutation
BUDGET_START = 4.0      # seconds per attempt at first
BUDGET_CAP = 12.0       # cap on per-attempt seconds as attempts keep failing
WINDOW = 6              # number of N values sampled above the lower bound
BIG = 100000            # penalty base for duplicate darts
A_CHOICES = (2, 3, 1, 4, 5)   # base-graph sizes per side, cycled through


# ----------------------------------------------------------------------------
# Safe baseline families (checked with lib.is_valid before acceptance).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New family: bipartite voltage lifts over small base multigraphs.
#
# Base: a vertices on side A (A_0..A_{a-1}) and a on side B. The base has d
# permutations sigma_k of range(a); dart (i, sigma_k(i), g) with voltage g in a
# finite group G of order N. Lift: vertex A_{i,x} is joined to B_{j, x*g} for
# every dart (i, j, g). The lift is d-regular, bipartite, has 2*a*N vertices.
#
# Left multiplication by h is an automorphism of the lift, so it suffices to
# check eccentricities of the 2a sources A_{i,e}, B_{j,e}.
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


def _darts(a, d, perms, volt):
    return [(i, perms[k][i], volt[k][i]) for k in range(d) for i in range(a)]


def _unreached(a, N, T, invs, D, darts):
    """Total count of (source, vertex) pairs at distance > D over the 2a sources."""
    out_adj = [[] for _ in range(a)]
    in_adj = [[] for _ in range(a)]
    for i, j, g in darts:
        out_adj[i].append((a + j, g))        # A_i -> block a+j, voltage g
        in_adj[j].append((i, invs[g]))       # B_j -> A_i, inverse voltage
    V = 2 * a * N
    total = 0
    for src in range(2 * a):
        seen = bytearray(V)
        s0 = src * N
        seen[s0] = 1
        frontier = [s0]
        count = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                b, x = divmod(v, N)
                row = T[x]
                if b < a:
                    for blk, g in out_adj[b]:
                        w = blk * N + row[g]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    for i, ig in in_adj[b - a]:
                        w = i * N + row[ig]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(a, d, N, T, invs, D, rng, iters, deadline):
    """Anneal base permutations and voltages to zero unreached pairs."""
    perms = []
    for _ in range(d):
        p = list(range(a))
        rng.shuffle(p)
        perms.append(p)
    volt = [[rng.randrange(N) for _ in range(a)] for _ in range(d)]

    def cost(pm, vt):
        darts = _darts(a, d, pm, vt)
        dup = len(darts) - len(set(darts))
        if dup:
            return BIG + dup
        return _unreached(a, N, T, invs, D, darts)

    cur = cost(perms, volt)
    for it in range(iters):
        if cur == 0:
            return perms, volt
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        k = rng.randrange(d)
        i = rng.randrange(a)
        np_ = [p[:] for p in perms]
        nv = [r[:] for r in volt]
        if a >= 2 and rng.random() < SWAP_MOVE:
            j = rng.randrange(a - 1)
            if j >= i:
                j += 1
            np_[k][i], np_[k][j] = np_[k][j], np_[k][i]
        else:
            if rng.random() < GROUP_MOVE:
                flat = [g for row in volt for g in row]
                c = T[rng.choice(flat)][rng.choice(flat)]
            else:
                c = rng.randrange(N)
            nv[k][i] = c
        nc = cost(np_, nv)
        if nc <= cur or rng.random() < math.exp(-(nc - cur) / temp):
            perms, volt, cur = np_, nv, nc
    if cur == 0:
        return perms, volt
    return None


def _edges(a, d, N, T, perms, volt):
    edges = []
    for k in range(d):
        for i in range(a):
            j = perms[k][i]
            g = volt[k][i]
            for x in range(N):
                edges.append((i * N + x, (a + j) * N + T[x][g]))
    return 2 * a * N, edges


def _attempt(a, d, N, D, rng, deadline):
    """Try groups of order N for base size a; return (n, edges) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        res = _anneal(a, d, N, T, invs, D, rng, ITERS, deadline)
        if res is not None:
            perms, volt = res
            return _edges(a, d, N, T, perms, volt)
    return None


def _family(d, D, rng, deadline, consider, best):
    """Repeatedly try (a, N) pairs whose vertex count would beat the current best."""
    moore = lib._moore_bound(d, D)
    budget = BUDGET_START
    while time.monotonic() < deadline:
        progressed = False
        tried = False
        for a in A_CHOICES:
            now = time.monotonic()
            if now >= deadline:
                break
            Vlo = max(best[0] + 1, int(0.45 * moore))
            Nlo = -(-Vlo // (2 * a))
            Nhi = moore // (2 * a)
            if Nlo > Nhi:
                continue
            tried = True
            N = rng.randint(Nlo, min(Nhi, Nlo + WINDOW))
            res = _attempt(a, d, N, D, rng, min(deadline, now + budget))
            if res is not None:
                consider(*res)
                progressed = True
        if not tried:
            break
        if not progressed:
            budget = min(BUDGET_CAP, budget * 1.5)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 8.0))

    if d < 1 or D < 1:
        return 1, []

    rng = random.Random(seed)
    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best[0], best[1]

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

    if d >= 3 and D >= 2 and time.monotonic() < deadline:
        _family(d, D, rng, deadline, consider, best)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
