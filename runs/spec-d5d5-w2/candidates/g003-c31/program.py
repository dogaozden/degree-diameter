import math
import random
import time

import lib

# Multi-orbit voltage lifts over semidirect products.
#
# The parent searches bi-Cayley graphs, which have a single A-orbit and a single
# B-orbit under the group. Here the base graph has k A-vertices and k B-vertices,
# each of degree d, and the base darts (i, j, g) carry group voltages g. The lift
# has vertices A(i, x) and B(j, y) for x, y in G, with edges
#     A(i, x) -- B(j, x*g)   for every dart (i, j, g).
# Left multiplication by G is an automorphism, so the eccentricities only need
# BFS from the 2k sources A(i, e) and B(j, e). The order is 2kN, where |G| = N.
# The base pairing and the voltages are annealed together.

ITERS = 1500
T_HOT = 1.0
T_COLD = 0.1
MAX_GROUPS = 10
K_LIST = (2, 3, 4, 1)   # orbit counts per side tried in rotation


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


def _cost(k, N, darts, T, D):
    """Number of (source, vertex) pairs at distance more than D over the 2k base sources."""
    kN = k * N
    V = 2 * kN
    adj = [[] for _ in range(V)]
    for i, j, g in darts:
        ai = i * N
        bj = kN + j * N
        for x in range(N):
            a = ai + x
            b = bj + T[x][g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for s in list(range(0, kN, N)) + list(range(kN, V, N)):
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(k, N, d, D, T, rng, deadline):
    """Anneal base pairing and voltages to make the lift diameter <= D. Returns darts or None."""
    a_side = [i for i in range(k) for _ in range(d)]
    b_side = [j for j in range(k) for _ in range(d)]
    rng.shuffle(b_side)
    darts = []
    used = set()
    for i, j in zip(a_side, b_side):
        while True:
            g = rng.randrange(N)
            if (i, j, g) not in used:
                break
        used.add((i, j, g))
        darts.append((i, j, g))

    cur = _cost(k, N, darts, T, D)
    for it in range(ITERS):
        if cur == 0:
            return darts
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        t = rng.randrange(len(darts))
        new = list(darts)
        if rng.random() < 0.6:
            i, j, _ = darts[t]
            new[t] = (i, j, rng.randrange(N))
        else:
            u = rng.randrange(len(darts))
            i1, j1, g1 = darts[t]
            i2, j2, g2 = darts[u]
            if j1 == j2:
                continue
            new[t] = (i1, j2, g1)
            new[u] = (i2, j1, g2)
        if len(set(new)) != len(new):
            continue
        v = _cost(k, N, new, T, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = new, v
    return darts if cur == 0 else None


def _attempt(k, N, d, D, rng, deadline):
    """Try groups of order N for the k-orbit base graph until one works or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        darts = _anneal(k, N, d, D, T, rng, deadline)
        if darts is not None:
            return T, darts
    return None


def _edges(k, N, T, darts):
    kN = k * N
    return [(i * N + x, kN + j * N + T[x][g]) for i, j, g in darts for x in range(N)]


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact record case for D = 3.
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

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    budgets = {}
    fails = {}

    while time.monotonic() < deadline:
        for k in K_LIST:
            if time.monotonic() >= deadline:
                break
            cap = moore // (2 * k)
            lo = max(d + 1, best[0] // (2 * k) + 1)   # need 2*k*N > best order
            if lo > cap:
                continue
            width = 6 + 2 * fails.get(k, 0)
            hi = min(cap, lo + width)
            Ns = list(range(lo, hi + 1))
            rng.shuffle(Ns)
            budget = budgets.get(k, 0.5)
            ok = False
            for N in Ns:
                now = time.monotonic()
                if now >= deadline:
                    break
                res = _attempt(k, N, d, D, rng, min(deadline, now + budget))
                if res is None:
                    continue
                T, darts = res
                consider(2 * k * N, _edges(k, N, T, darts))
                ok = True
                break
            if ok:
                fails[k] = 0
            else:
                fails[k] = fails.get(k, 0) + 1
                budgets[k] = min(4.0, budget * 1.5)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
