"""Multi-orbit voltage lifts over semidirect groups.

New idea (not in the parent): instead of one bi-Cayley orbit pair (2 base vertices),
use a base bipartite graph with `a` vertices on each side, where every base vertex
has degree d. Its d darts form d permutation matchings sigma_k, and each dart
(sigma_k, i) carries a group voltage volt[k][i]. The lift over a group G of order N
has 2aN vertices. Left multiplication by G is an automorphism that acts regularly on
each fibre, so the diameter is decided by BFS from the a + a identity vertices only.
Annealing moves change voltages and permutations, and the cost counts unreached
pairs plus a penalty for parallel darts with equal voltage.
"""
import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _cost(a, N, d, D, T, sig, volt):
    """Unreached (source, vertex) pairs over the a+a identity sources, plus a penalty for parallel darts."""
    V = 2 * a * N
    adj = [[] for _ in range(V)]
    pairs = [set() for _ in range(a * a)]
    dup = 0
    for k in range(d):
        sk = sig[k]
        vk = volt[k]
        for i in range(a):
            j = sk[i]
            g = vk[i]
            ps = pairs[i * a + j]
            if g in ps:
                dup += 1
            else:
                ps.add(g)
            ua = i * N
            ub = (a + j) * N
            for x in range(N):
                y = T[x][g]
                adj[ua + x].append(ub + y)
                adj[ub + y].append(ua + x)
    total = 0
    srcs = [i * N for i in range(a)] + [(a + j) * N for j in range(a)]
    for s in srcs:
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
    return total + 300 * dup


def _anneal(a, N, d, D, T, rng, deadline):
    """Anneal permutations and voltages until the lift has diameter <= D."""
    sig = [rng.sample(range(a), a) for _ in range(d)]
    volt = [[rng.randrange(N) for _ in range(a)] for _ in range(d)]
    cur = _cost(a, N, d, D, T, sig, volt)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now > deadline:
            break
        frac = (now - t0) / span
        temp = max(0.2, 3.0 * (1.0 - frac))
        nsig = [s[:] for s in sig]
        nvolt = [v[:] for v in volt]
        k = rng.randrange(d)
        if a > 1 and rng.random() < 0.2:
            i1, i2 = rng.sample(range(a), 2)
            nsig[k][i1], nsig[k][i2] = nsig[k][i2], nsig[k][i1]
        else:
            nvolt[k][rng.randrange(a)] = rng.randrange(N)
        c2 = _cost(a, N, d, D, T, nsig, nvolt)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            sig, volt, cur = nsig, nvolt, c2
    return (sig, volt) if cur == 0 else None


def _edges(a, N, d, sig, volt, T):
    E = []
    for k in range(d):
        for i in range(a):
            j = sig[k][i]
            g = volt[k][i]
            for x in range(N):
                E.append((i * N + x, (a + j) * N + T[x][g]))
    return E


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

    consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d >= 2 and D >= 2:
        try_budget = 3.0
        while time.monotonic() < deadline:
            a = rng.choice([2, 2, 3, 3, 4])
            n_min = best_n // (2 * a) + 1
            N = max(2, n_min + rng.randrange(0, 3))
            gs = _groups(N)
            m, k, r = rng.choice(gs)
            order, mul, inv = lib.semidirect_group(m, k, r)
            T = [[mul(x, g) for g in range(N)] for x in range(N)]
            tdl = min(deadline, time.monotonic() + try_budget)
            res = _anneal(a, N, d, D, T, rng, tdl)
            if res is not None:
                sig, volt = res
                consider(2 * a * N, _edges(a, N, d, sig, volt, T))

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
