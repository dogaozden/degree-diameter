import itertools
import math
import random
import time

import lib

ITERS = 400          # annealing steps per (group, base-layout) try
T_HOT = 1.2          # initial annealing temperature (in unreached-pair units)
T_COLD = 0.1         # final annealing temperature
MAX_GROUPS = 6       # groups tried per attempt
LAYER_KS = (2, 3)    # base orbits per side: k A-vertices and k B-vertices
MAX_BUDGET = 15.0    # cap on the per-target time budget (seconds)


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
# Multi-orbit bi-Cayley lifts (new construction).
#
# Base graph: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}, with d
# layers of darts. Layer l is a permutation p_l of {0..k-1}; dart (i, p_l(i), g)
# joins A_i,x to B_{p_l(i)}, x*g for every x in G. Every base vertex has degree
# d, so the lift is d-regular bipartite on 2kN vertices (before duplicate
# removal). Left multiplication by G is an automorphism, so the diameter is
# controlled by BFS from one source per base orbit, i.e. 2k sources.
#
# Moves: change the group label of one dart, or swap the target of two darts
# in the same layer (keeps every layer a permutation, so degrees stay d).
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


def _random_darts(N, k, d, rng):
    """Darts as [i, j, g]; index l*k + i holds the dart of layer l starting at A_i."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(N)])
    return darts


def _build_nbrs(N, k, darts, T, invs):
    """Neighbour lists of the lifted graph. A(i,x) = i*N+x, B(j,y) = k*N + j*N + y."""
    V = 2 * k * N
    base_b = k * N
    Aadj = [[] for _ in range(k)]
    Badj = [[] for _ in range(k)]
    for i, j, g in darts:
        Aadj[i].append((j, g))
        Badj[j].append((i, invs[g]))
    nb = [None] * V
    for i in range(k):
        for x in range(N):
            Tx = T[x]
            nb[i * N + x] = [base_b + j * N + Tx[g] for j, g in Aadj[i]]
    for j in range(k):
        for y in range(N):
            Ty = T[y]
            nb[base_b + j * N + y] = [i * N + Ty[h] for i, h in Badj[j]]
    return V, nb


def _cost(N, k, D, darts, T, invs):
    """Total number of (source, vertex) pairs at distance > D, over one source per base orbit."""
    V, nb = _build_nbrs(N, k, darts, T, invs)
    srcs = [i * N for i in range(k)] + [k * N + j * N for j in range(k)]
    total = 0
    for s in srcs:
        seen = bytearray(V)
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
        total += V - count
    return total


def _anneal(N, k, d, D, T, invs, rng, deadline):
    """Anneal dart labels and layer permutations to zero unreached pairs; return darts or None."""
    darts = _random_darts(N, k, d, rng)
    cur = _cost(N, k, D, darts, T, invs)
    for it in range(ITERS):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        new = [list(x) for x in darts]
        if rng.random() < 0.7:
            a = rng.randrange(len(new))
            new[a][2] = rng.randrange(N)
        else:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            a, b = l * k + i1, l * k + i2
            new[a][1], new[b][1] = new[b][1], new[a][1]
        v = _cost(N, k, D, new, T, invs)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = new, v
    if cur == 0:
        return darts
    return None


def _attempt(N, k, d, D, rng, deadline):
    """Try groups of order N until one gives a valid multi-orbit lift, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        darts = _anneal(N, k, d, D, T, invs, rng, deadline)
        if darts is not None:
            return darts, T
    return None


def _lift_edges(N, k, darts, T):
    """Edge list of the lift: A(i,x) -- B(j, x*g) for each dart (i, j, g)."""
    base_b = k * N
    E = set()
    for i, j, g in darts:
        for x in range(N):
            E.add((i * N + x, base_b + j * N + T[x][g]))
    return 2 * k * N, sorted(E)


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
    targets = {}
    budget = {}
    for k in LAYER_KS:
        hi = moore // (2 * k)
        lo = best_n // (2 * k) + 1
        targets[k] = max(lo, int(0.45 * hi), 2)
        budget[k] = 0.5
    active = list(LAYER_KS)

    while time.monotonic() < deadline and active:
        for k in list(active):
            now = time.monotonic()
            if now >= deadline:
                break
            # Targets always aim above the current best for this k.
            targets[k] = max(targets[k], best_n // (2 * k) + 1)
            N = targets[k]
            if 2 * k * N > moore or N < 2:
                active.remove(k)
                continue
            att_deadline = min(deadline, now + budget[k])
            res = _attempt(N, k, d, D, rng, att_deadline)
            if res is None:
                budget[k] = min(MAX_BUDGET, budget[k] * 1.5)
                continue
            darts, T = res
            n, e = _lift_edges(N, k, darts, T)
            consider(n, e)
            targets[k] = N + 1
            budget[k] = 0.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
