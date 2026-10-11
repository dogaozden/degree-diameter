import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 6   # groups tried for one (k, N) pair within one attempt
ITERS = 400                  # annealing steps per group
ATTEMPT_BUDGET = 1.5         # seconds per (k, N) attempt
POOL = 8                     # how many smallest sizes above the incumbent to sample from


# ----------------------------------------------------------------------------
# Baselines (fast, always valid when they pass lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit voltage lifts over semidirect products.
#
# New in this version: the base graph has k "A" vertices and k "B" vertices,
# and is d-regular, given by d permutations sigma_t of range(k). Dart (t, i)
# joins A_i to B_{sigma_t(i)} with voltage g = volt[t][i] in a group G of order N.
# Lift vertices are A_{i,x} and B_{j,y} (x, y in G):
#     A_{i,x} ~ B_{sigma_t(i), x*volt[t][i]}   for each t.
# Left multiplication by G is an automorphism, so BFS from the k A-representatives
# A_{i,e} and the k B-representatives B_{j,e} decides the diameter.
# Order = 2*k*N. k = 1 is the plain bi-Cayley search over a single orbit pair.
# The search anneals over sigma and volt jointly to minimise unreached pairs.
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


def _inv_perm(p):
    q = [0] * len(p)
    for i, v in enumerate(p):
        q[v] = i
    return q


def _unreached(k, N, d, D, T, invs, sigma, volt):
    """Total count of (source, vertex) pairs at distance > D, over the 2k base representatives."""
    V = 2 * k * N
    kN = k * N
    sinv = [_inv_perm(sigma[t]) for t in range(d)]
    adj = [None] * V
    for i in range(k):
        for x in range(N):
            row = []
            for t in range(d):
                j = sigma[t][i]
                row.append(kN + j * N + T[x][volt[t][i]])
            adj[i * N + x] = row
    for j in range(k):
        for y in range(N):
            row = []
            for t in range(d):
                i = sinv[t][j]
                g = volt[t][i]
                row.append(i * N + T[y][invs[g]])
            adj[kN + j * N + y] = row

    sources = [i * N for i in range(k)] + [kN + j * N for j in range(k)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
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


def _anneal(k, N, d, D, T, invs, rng, iters, deadline):
    """Anneal over (sigma, volt) to zero unreached pairs; return (sigma, volt) or None."""
    sigma = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        sigma.append(p)
    volt = [[rng.randrange(N) for _ in range(k)] for _ in range(d)]
    cur = _unreached(k, N, d, D, T, invs, sigma, volt)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        if k > 1 and rng.random() < 0.1:
            t = rng.randrange(d)
            new_sigma = [p[:] for p in sigma]
            rng.shuffle(new_sigma[t])
            new_volt = volt
        else:
            t = rng.randrange(d)
            i = rng.randrange(k)
            new_sigma = sigma
            new_volt = [row[:] for row in volt]
            new_volt[t][i] = rng.randrange(N)
        v = _unreached(k, N, d, D, T, invs, new_sigma, new_volt)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            sigma, volt, cur = new_sigma, new_volt, v
    if cur == 0:
        return sigma, volt
    return None


def _attempt(k, N, d, D, rng, deadline):
    """Try groups of order N for k-orbit lifts until one gives diameter <= D or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        res = _anneal(k, N, d, D, T, invs, rng, ITERS, deadline)
        if res is not None:
            return T, res
    return None


def _lift_edges(k, N, d, T, sigma, volt):
    """Edge list of the lift; vertices A_i,x -> i*N+x and B_j,y -> k*N + j*N + y."""
    kN = k * N
    edges = set()
    for i in range(k):
        for x in range(N):
            a = i * N + x
            for t in range(d):
                j = sigma[t][i]
                b = kN + j * N + T[x][volt[t][i]]
                edges.add((min(a, b), max(a, b)))
    return sorted(edges)


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

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    # All candidate (order, k, N) with order = 2*k*N within the Moore bound, k = 1..4.
    sizes = []
    for k in range(1, 5):
        for N in range(2, moore // (2 * k) + 1):
            n2 = 2 * k * N
            if n2 <= moore:
                sizes.append((n2, k, N))
    sizes.sort()

    budget = ATTEMPT_BUDGET
    while time.monotonic() < deadline:
        cands = [s for s in sizes if s[0] > best_n]
        if not cands:
            break
        n2, k, N = rng.choice(cands[:POOL])
        now = time.monotonic()
        att_deadline = min(deadline, now + budget)
        res = _attempt(k, N, d, D, rng, att_deadline)
        if res is None:
            budget = min(budget * 1.1, 6.0)
            continue
        T, (sigma, volt) = res
        edges = _lift_edges(k, N, d, T, sigma, volt)
        consider(2 * k * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
