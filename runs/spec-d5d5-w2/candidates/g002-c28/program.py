"""Bi-Cayley lift search with greedy-seeded annealing for bipartite graphs of max degree d and diameter <= D.

Changes from the parent: the D >= 4 families are replaced by a single bi-Cayley engine
(vertices A_x, B_y over a semidirect group G, A_x ~ B_{x g} for g in S). Each candidate
connection set S is seeded by a greedy coverage build (choose elements that minimise the
number of unreached pairs), then refined by simulated annealing on swaps. Left translation
is an automorphism, so only the eccentricities of A_0 and B_0 need checking. Every returned
graph passes lib.is_valid, with K_{d,d} (or C_{2D} for d = 2, or PG(2, d-1) for D >= 3 when
d-1 is a prime power) as a fallback.
"""
import math
import random
import time

import lib


MAX_GROUPS = 6          # groups tried per group order N before moving on
ANNEAL_ITERS = 1500     # annealing steps per group
GREEDY_SAMPLE = 24      # candidates sampled per greedy step
_TABLE_CACHE = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m * k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Cached (T, invs): T[x][g] = x*g and invs[g] = g^-1 for Z_m x|_r Z_k."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (T, invs)
    if len(_TABLE_CACHE) >= 24:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Number of (source, vertex) pairs at distance > D, for sources A_0 and B_0."""
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


def _greedy(N, T, invs, d, D, rng, deadline):
    """Build S = [0, ...] of size d, adding at each step the sampled element that reaches the most pairs."""
    S = [0]
    while len(S) < d:
        if time.monotonic() > deadline:
            return None
        inS = set(S)
        pool = [c for c in range(1, N) if c not in inS]
        cs = rng.sample(pool, min(GREEDY_SAMPLE, len(pool)))
        best_c, best_v = None, None
        for c in cs:
            v = _unreached(N, T, invs, S + [c], D)
            if best_v is None or v < best_v or (v == best_v and rng.random() < 0.3):
                best_v, best_c = v, c
        S.append(best_c)
    return S


def _search(N, T, invs, d, D, rng, deadline):
    """Greedy seed followed by annealed single-element swaps (index 0 fixed to identity)."""
    S = _greedy(N, T, invs, d, D, rng, deadline)
    if S is None:
        return None
    cur = _unreached(N, T, invs, S, D)
    if cur == 0:
        return S
    best_S, best_v = list(S), cur
    T0 = 2.0 + 0.05 * cur
    T_end = 0.2
    decay = (T_end / T0) ** (1.0 / ANNEAL_ITERS)
    temp = T0
    for _ in range(ANNEAL_ITERS):
        if best_v == 0 or time.monotonic() > deadline:
            break
        temp = max(T_end, temp * decay)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur < best_v:
                best_S, best_v = list(S), cur
    return best_S if best_v == 0 else None


def _cycle(D):
    n = 2 * D
    return n, [(i, (i + 1) % n) for i in range(n)]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        return _cycle(D)

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Projective plane baseline (diameter 3) when d - 1 is a small prime power.
    if D >= 3 and d - 1 <= 23 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    tried = {}
    try:
        while best[0] < moore and time.monotonic() < deadline:
            lo = best[0] // 2 + 1
            if lo > moore // 2:
                break
            window = max(2, lo // 10)
            hi = min(lo + window, moore // 2 + 1)
            if hi <= lo or lo < d:
                break
            N = min(range(lo, hi), key=lambda x: (tried.get(x, 0), rng.random()))
            tried[N] = tried.get(N, 0) + 1
            groups = _groups(N)
            rng.shuffle(groups)
            for m, k2, r in groups[:MAX_GROUPS]:
                if time.monotonic() > deadline:
                    break
                T, invs = _tables(m, k2, r)
                S = _search(N, T, invs, d, D, rng, deadline)
                if S is not None:
                    edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                    consider(2 * N, edges)
                    break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
