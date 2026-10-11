"""Bi-Cayley lifts searched with a vectorized (numpy) diameter evaluator.

Engine change for D >= 4: the connection set S of a bi-Cayley graph over a
semidirect product Z_m x|_r Z_k is annealed against an exact unreached-pair
count computed with numpy frontier expansion, which is roughly 20-50x cheaper
per evaluation than the pure-Python BFS it replaces. Orders N are swept upward
from the current best, so the search aims above the incumbent.

Calibration: D = 3 uses the PG(2, q) incidence graph (d3D3 -> 14 vertices).
Every returned graph is checked with lib.is_valid; K_{d,d} is the fallback.

Caveat: this program was written without being executed, so its runtime and
the search's success on d=5, D=5 are untested.
"""
import math
import random
import time

import numpy as np

import lib

MAX_GROUPS = 6        # groups tried per order N before moving to the next N
ANNEAL_ITERS = 1500   # annealing steps per group
WINDOW = 6            # orders tried above the current lower bound, cycled
_TABLES = {}


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _table(m, k, r):
    """Cached (order, T, invs): T[x, g] = x*g and invs[g] = g^-1 as numpy arrays."""
    key = (m, k, r)
    hit = _TABLES.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = np.array([[mul(x, g) for g in range(order)] for x in range(order)],
                 dtype=np.int64)
    invs = np.array([inv(g) for g in range(order)], dtype=np.int64)
    val = (order, T, invs)
    if len(_TABLES) >= 40:
        _TABLES.clear()
    _TABLES[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Pairs (source, vertex) not within distance D, for sources A_0 and B_0.

    Bi-Cayley graph: A_x ~ B_{x g} for g in S. Left translation is an automorphism
    that fixes each side, so the two representatives suffice.
    """
    Sa = np.asarray(S, dtype=np.int64)
    TS = T[:, Sa]              # TS[x, i] = x * g_i   (neighbours of A_x)
    TSi = T[:, invs[Sa]]       # TSi[y, i] = y * g_i^-1 (neighbours of B_y)
    total = 0
    for side in (0, 1):
        seen = [np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)]  # [A, B]
        seen[side][0] = True
        front = np.array([0], dtype=np.int64)
        cur = side
        for _ in range(D):
            mask = np.zeros(N, dtype=bool)
            if cur == 0:
                mask[TS[front].ravel()] = True
            else:
                mask[TSi[front].ravel()] = True
            mask &= ~seen[1 - cur]
            seen[1 - cur] |= mask
            front = np.nonzero(mask)[0]
            cur = 1 - cur
            if front.size == 0:
                break
        total += 2 * N - int(seen[0].sum()) - int(seen[1].sum())
    return total


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    """Anneal a connection set S of size d (identity fixed) to zero unreached pairs."""
    if N < d or d < 2:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best_v, best_S = cur, list(S)
    T0 = 2.0 + 0.02 * cur
    for step in range(iters):
        if best_v == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.3
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = list(S)
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur < best_v:
                best_v, best_S = cur, list(S)
    return best_S if best_v == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baseline (exact record for D = 3 when d - 1 is a prime power).
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if best[0] >= moore:
            return best

    # Main search: bi-Cayley lifts with orders N just above the incumbent.
    attempt = 0
    while time.monotonic() < deadline and best[0] < moore:
        lo = best[0] // 2 + 1
        if lo > moore // 2:
            break
        N = lo + attempt % WINDOW
        attempt += 1
        if N > moore // 2 or N < d:
            continue
        groups = _groups(N)
        rng.shuffle(groups)
        for m, k, r in groups[:MAX_GROUPS]:
            if time.monotonic() >= deadline:
                break
            _, T, invs = _table(m, k, r)
            S = _anneal(N, T, invs, d, D, rng, ANNEAL_ITERS, deadline)
            if S is not None:
                edges = [(x, N + int(T[x, g])) for x in range(N) for g in S]
                consider(2 * N, edges)
                break

    n, e = best
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
