import math
import random
import time

import lib

MAX_GROUPS = 10      # groups tried per order N before resampling N
ANNEAL_ITERS = 4000  # annealing steps per (group, N) attempt
N_WINDOW = 6         # candidate orders N in [record//2 + 1, record//2 + N_WINDOW]
_CACHE = {}


def _pg_baseline(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_specs(N):
    """Specs for groups of order N: abelian Z_a x Z_b (a <= b) and semidirect Z_m x|_r Z_k with r != 1."""
    specs = []
    for a in range(1, N + 1):
        if N % a == 0:
            b = N // a
            if a <= b:
                specs.append(("ab", a, b))
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                specs.append(("sd", m, k, r))
    return specs


def _group(spec):
    """Return (N, T, invs) with T[x][g] = x*g and invs[g] = g^-1; cached per spec."""
    hit = _CACHE.get(spec)
    if hit is not None:
        return hit
    if spec[0] == "ab":
        _, a, b = spec
        N = a * b

        def mul(x, y):
            i1, j1 = divmod(x, b)
            i2, j2 = divmod(y, b)
            return ((i1 + i2) % a) * b + (j1 + j2) % b

        def inv(x):
            i, j = divmod(x, b)
            return ((-i) % a) * b + (-j) % b
    else:
        _, m, k, r = spec
        N, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    val = (N, T, invs)
    if len(_CACHE) >= 64:
        _CACHE.clear()
    _CACHE[spec] = val
    return val


def _unreached(N, T, invs, S, D):
    """Pairs (source, target) at distance > D, from A_0 and B_0 of the bi-Cayley graph A_x ~ B_{x g}, g in S."""
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


def _anneal(N, T, invs, d, D, rng, deadline, iters):
    """Simulated annealing over S (identity fixed as one element) to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    t0, t1 = 1.5, 0.05
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = t0 * (t1 / t0) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = _unreached(N, T, invs, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            S[i] = old
    return list(S) if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is Moore-optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d <= 1:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _pg_baseline(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: bi-Cayley lifts (2N vertices) over many groups, sweeping N just above the record.
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = n_best // 2 + 1
        if 2 * lo > moore:
            break
        N = lo + rng.randrange(N_WINDOW)
        if 2 * N > moore:
            N = lo
        if N < d:
            continue

        specs = _group_specs(N)
        rng.shuffle(specs)
        found = None
        for spec in specs[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            Ng, T, invs = _group(spec)
            S = _anneal(Ng, T, invs, d, D, rng, deadline, ANNEAL_ITERS)
            if S is not None:
                found = (Ng, T, S)
                break
        if found is not None:
            Ng, T, S = found
            edges = [(x, Ng + T[x][g]) for x in range(Ng) for g in S]
            consider(2 * Ng, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
