import itertools
import math
import random
import time

import lib

ITERS = 1500                 # annealing steps per (group, base-graph) attempt
MAX_GROUPS = 25              # groups tried per attempt
TIME_FRACTION = 0.8          # use this fraction of time_limit
MAX_ORBITS = 4               # base graphs with a A-orbits and a B-orbits, a = 1..MAX_ORBITS


# ----------------------------------------------------------------------------
# Safe baseline families (returned if they pass lib.is_valid).
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
# New construction: multi-orbit voltage lifts over semidirect products.
#
# Base graph: a A-vertices and a B-vertices, d layers. Layer k is a permutation
# sigma_k of range(a) and voltages g_{k,i} in G. Dart (A_i, B_{sigma_k(i)}, g_{k,i})
# lifts to edges (A_i, x) -- (B_j, x*g) for all x in G. Left multiplication is an
# automorphism, so diameter <= D iff BFS from one vertex per base orbit reaches
# everything within D.  Order = 2*a*|G|; we search for orders above the best so far.
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


def _lift_adj(a, N, T, d, sigma, volt):
    """Adjacency lists of the lift. A-orbit i is ids i*N..i*N+N-1; B-orbit j is (a+j)*N.."""
    adj = [[] for _ in range(2 * a * N)]
    for k in range(d):
        sk = sigma[k]
        vk = volt[k]
        for i in range(a):
            j = sk[i]
            g = vk[i]
            ba = i * N
            bb = (a + j) * N
            for x in range(N):
                u = ba + x
                v = bb + T[x][g]
                adj[u].append(v)
                adj[v].append(u)
    return adj


def _cost(a, N, D, adj, sources):
    """Total number of (source, vertex) pairs not within distance D."""
    n = 2 * a * N
    total = 0
    for s in sources:
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += n - cnt
    return total


def _anneal(a, N, T, d, D, rng, iters, deadline):
    """Anneal base-graph permutations and voltages until the lift has diameter <= D."""
    sigma = [rng.sample(range(a), a) for _ in range(d)]
    volt = [[rng.randrange(N) for _ in range(a)] for _ in range(d)]
    sources = [o * N for o in range(2 * a)]

    def evaluate(sg, vt):
        keys = {(i, sg[k][i], vt[k][i]) for k in range(d) for i in range(a)}
        dup = d * a - len(keys)  # repeated darts would create duplicate edges
        adj = _lift_adj(a, N, T, d, sg, vt)
        return _cost(a, N, D, adj, sources) + 1000 * dup

    cur = evaluate(sigma, volt)
    for it in range(iters):
        if cur == 0:
            return sigma, volt
        if time.monotonic() > deadline:
            break
        temp = max(0.2, 3.0 * (1.0 - it / iters))
        k = rng.randrange(d)
        if a > 1 and rng.random() < 0.3:
            i1, i2 = rng.sample(range(a), 2)
            sg2 = [row[:] for row in sigma]
            sg2[k][i1], sg2[k][i2] = sg2[k][i2], sg2[k][i1]
            vt2 = volt
        else:
            i = rng.randrange(a)
            vt2 = [row[:] for row in volt]
            vt2[k][i] = rng.randrange(N)
            sg2 = sigma
        v = evaluate(sg2, vt2)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            sigma, volt, cur = sg2, vt2, v
    return (sigma, volt) if cur == 0 else None


def _search(a, N, d, D, rng, deadline):
    """Try groups of order N for a base graph with a orbits per side; return a valid lift or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        res = _anneal(a, N, T, d, D, rng, ITERS, deadline)
        if res is not None:
            sigma, volt = res
            return a, N, T, sigma, volt
    return None


def _lift_graph(a, N, T, d, sigma, volt):
    adj = _lift_adj(a, N, T, d, sigma, volt)
    edges = set()
    for u in range(len(adj)):
        for v in adj[u]:
            if u < v:
                edges.add((u, v))
    return 2 * a * N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + TIME_FRACTION * time_limit
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

    moore = lib._moore_bound(d, D)  # bound on total vertices

    # Per orbit-count a: a lift of order 2*a*N must exceed the current best.
    target = {}
    cap = {}
    budget = {}
    for a in range(1, MAX_ORBITS + 1):
        cap[a] = moore // (2 * a)
        target[a] = max(d + 1, best_n // (2 * a) + 1)
        budget[a] = 1.0
    active = [a for a in range(1, MAX_ORBITS + 1) if target[a] <= cap[a]]

    while active and time.monotonic() < deadline:
        for a in list(active):
            now = time.monotonic()
            if now >= deadline:
                break
            N = target[a]
            if N > cap[a]:
                active.remove(a)
                continue
            att_deadline = min(deadline, now + budget[a])
            res = _search(a, N, d, D, rng, att_deadline)
            if res is None:
                budget[a] = min(budget[a] * 1.4, 20.0)
                continue
            a_, N_, T, sigma, volt = res
            n, e = _lift_graph(a_, N_, T, d, sigma, volt)
            consider(n, e)
            # Success: move this orbit count to a larger group order.
            target[a] = N + 1
            budget[a] = 1.0

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
