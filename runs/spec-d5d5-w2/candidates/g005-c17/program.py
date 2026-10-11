import math
import random
import time

import lib


# Bi-Cayley lifts over semidirect products Z_m x|_r Z_k (one base vertex per side).
# A_x ~ B_{x*g} for g in S. Left translation is an automorphism, so eccentricities
# of A_0 and B_0 determine diameter. The connection set S is searched by simulated
# annealing on the number of unreached (source, target) pairs.

MAX_GROUPS = 12
ANNEAL_ITERS = 2500
N_WINDOW = 8
T_START = 3.0
T_END = 0.2


def _pg_baseline(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
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


def _unreached(N, T, invs, S, D):
    """Total unreached (source, target) pairs from A_0 and B_0; zero means diameter <= D."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        count = 1
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


def _anneal_S(N, T, invs, d, D, rng, deadline, iters):
    """Simulated annealing over S (identity fixed as one dart, WLOG). Returns S or None."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = _unreached(N, T, invs, S, D)
        delta = v - cur
        temp = max(T_END, T_START * (1.0 - it / iters))
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = v
        else:
            S[i] = old
    return list(S) if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and meets the Moore bound for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)
    rng = random.Random(seed)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _pg_baseline(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: bi-Cayley annealing with N sweeping just above the current record.
    while best[0] < moore and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(N_WINDOW)
        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for m, k, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            order, mul, inv = lib.semidirect_group(m, k, r)
            T = [[mul(x, g) for g in range(order)] for x in range(order)]
            invs = [inv(g) for g in range(order)]
            S = _anneal_S(N, T, invs, d, D, rng, deadline, ANNEAL_ITERS)
            if S is not None:
                found = (T, S)
                break
        if found is not None:
            T, S = found
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
