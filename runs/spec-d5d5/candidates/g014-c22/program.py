import math
import random
import time

import lib

MAX_GROUPS = 24     # groups tried per (N, attempt)
POOL_CAP = 48       # groups kept per order N
ITERS = 700         # annealing steps per (group, connection set)
T_HOT = 1.5         # initial annealing temperature (in unreached-pair units)
T_COLD = 0.15       # final annealing temperature
WINDOW = 6          # orders tried per pass, starting just above the best found
BUDGET_CAP = 8.0    # seconds, upper limit on a single attempt budget


# ----------------------------------------------------------------------------
# Baseline families, used as the safe fallback.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group pool. Bi-Cayley graphs over a group G of order N: vertices A_x, B_y
# (x, y in G), edges A_x -- B_{x s} for s in S. Groups are (order, mul, inv).
# Besides metacyclic groups Z_m x|_r Z_k, we also use direct products of two
# smaller groups, which widens the pool beyond the parent's metacyclic-only set.
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


def _direct(G1, G2):
    """Direct product of two groups given as (order, mul, inv); element index = a*n2 + b."""
    n1, m1, i1 = G1
    n2, m2, i2 = G2

    def mul(x, y):
        a, b = divmod(x, n2)
        c, d = divmod(y, n2)
        return m1(a, c) * n2 + m2(b, d)

    def inv(x):
        a, b = divmod(x, n2)
        return i1(a) * n2 + i2(b)

    return n1 * n2, mul, inv


def _small(n, rng, cap):
    """Up to cap semidirect groups of order n, sampled at random."""
    params = _groups(n)
    rng.shuffle(params)
    return [lib.semidirect_group(m, k, r) for (m, k, r) in params[:cap]]


def _pool(N, rng):
    """A shuffled list of groups of order N: metacyclic ones plus direct products."""
    pool = [lib.semidirect_group(m, k, r) for (m, k, r) in _groups(N)]
    for N1 in range(2, N // 2 + 1):
        if N % N1 == 0 and N // N1 >= 2:
            A = _small(N1, rng, 3)
            B = _small(N // N1, rng, 3)
            for a in A:
                for b in B:
                    pool.append(_direct(a, b))
    rng.shuffle(pool)
    return pool[:POOL_CAP]


# ----------------------------------------------------------------------------
# Search: annealing over S = {0, s_1, ..., s_{d-1}} to minimise the number of
# (source, vertex) pairs at distance more than D. Sources A_0 and B_0 suffice
# because left multiplication is an automorphism acting transitively on each side.
# ----------------------------------------------------------------------------

def _unreached(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S containing identity; returns S with zero unreached pairs or None."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    if cur == 0:
        return S
    return None


def _attempt(N, d, D, rng, deadline, pool):
    """Try a random sample of groups of order N until one yields diameter <= D, or time runs out."""
    cands = rng.sample(pool, min(len(pool), MAX_GROUPS))
    for n, mul, inv in cands:
        if time.monotonic() > deadline:
            return None
        T = [[mul(x, g) for g in range(n)] for x in range(n)]
        invs = [inv(g) for g in range(n)]
        S = _anneal(n, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Record-matching case for D = 3: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    # Safe fallbacks.
    consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    # Bi-Cayley search: a graph on 2N vertices with N up to Moore/2.
    Nmax = lib._moore_bound(d, D) // 2
    best_N = 0
    budget = 0.3
    pools = {}

    while time.monotonic() < deadline and best_N < Nmax:
        progressed = False
        lo = max(d + 1, best_N + 1)
        hi = min(Nmax, best_N + WINDOW)
        for N in range(lo, hi + 1):
            now = time.monotonic()
            if now >= deadline:
                break
            if N not in pools:
                pools[N] = _pool(N, rng)
            if not pools[N]:
                continue
            att_deadline = min(deadline, now + budget)
            res = _attempt(N, d, D, rng, att_deadline, pools[N])
            if res is None:
                continue
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            before = best[0]
            consider(2 * N, edges)
            if best[0] > before:
                best_N = N
                progressed = True
                break
        if not progressed:
            budget = min(budget * 2, BUDGET_CAP)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
