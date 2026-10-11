import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Strategy for this island:
#   * D = 2: K_{d,d} (meets the Moore bound).
#   * D = 3: incidence graph of PG(2, q) for the largest prime power q <= d-1.
#   * D >= 4 (target d=5, D=5): bi-Cayley lifts over semidirect products
#     Z_m x|_r Z_k. A lift of order N gives 2N vertices, each side of degree d.
#     Connection sets are found by simulated annealing, with cost equal to the
#     number of (source, vertex) pairs left beyond distance D. Sources are the
#     two base vertices A_0 and B_0, which suffices by left-translation symmetry.
#     Reach is computed with vectorised numpy BFS over the whole frontier.
#     N sweeps upward from just below the record order 168 (order 336), so the
#     search aims at N >= 169.
#   * Every candidate is checked with lib.is_valid. Fallback is K_{d,d}.
# ----------------------------------------------------------------------------

MAX_N_SEARCH = 1500     # cap on lift order N (table size N^2)
SLICE = 3.0             # seconds spent on each N before moving to N+1
ANNEAL_ITERS = 2500     # annealing steps per attempt
_cache = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N giving Z_m x|_r Z_k."""
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
    """Vectorised multiplication table T[x, g] = x*g and inverse array for Z_m x|_r Z_k."""
    N = m * k
    xs = np.arange(N, dtype=np.int64)
    a = xs // k
    b = xs % k
    pw = np.array([pow(r, bb, m) for bb in range(k)], dtype=np.int64)
    A = a[:, None]
    Bb = b[:, None]
    C = a[None, :]
    Dd = b[None, :]
    T = ((A + pw[Bb] * C) % m) * k + (Bb + Dd) % k
    nb = (-b) % k
    invs = ((-pw[nb] * a) % m) * k + nb
    return T.astype(np.int64), invs.astype(np.int64)


def _cached_table(m, k, r):
    key = (m, k, r)
    if key not in _cache:
        if len(_cache) > 64:
            _cache.clear()
        _cache[key] = _table(m, k, r)
    return _cache[key]


def _reach_cost(N, T, invs, S, D):
    """Unreached (source, vertex) pairs from A_0 and B_0 within distance D. Zero means valid.

    Bi-Cayley graph: A_x ~ B_{x g} for g in S. So A_x's neighbours are T[x, g],
    and B_v's neighbours are A_x with x = v g^{-1}, i.e. T[v, g^{-1}].
    """
    Sa = np.asarray(S, dtype=np.int64)
    Si = invs[Sa]
    total = 0
    for side in (0, 1):
        seenA = np.zeros(N, dtype=bool)
        seenB = np.zeros(N, dtype=bool)
        if side == 0:
            seenA[0] = True
            fA = np.array([0], dtype=np.int64)
            fB = np.empty(0, dtype=np.int64)
        else:
            seenB[0] = True
            fA = np.empty(0, dtype=np.int64)
            fB = np.array([0], dtype=np.int64)
        for _ in range(D):
            if fA.size == 0 and fB.size == 0:
                break
            cb = T[fA][:, Sa].ravel()
            ca = T[fB][:, Si].ravel()
            cb = np.unique(cb[~seenB[cb]])
            ca = np.unique(ca[~seenA[ca]])
            seenB[cb] = True
            seenA[ca] = True
            fA, fB = ca, cb
        total += 2 * N - int(seenA.sum()) - int(seenB.sum())
    return total


def _anneal_S(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over connection sets S (identity fixed in S, WLOG)."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _reach_cost(N, T, invs, S, D)
    t0, t1 = 2.0, 0.2
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
        S2 = S[:]
        S2[i] = c
        v = _reach_cost(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _search(d, D, moore, deadline, rng, cur_n, consider):
    """Sweep bi-Cayley lift orders N upward from just below the record range."""
    lo = max(d, cur_n // 2 + 1, int(0.45 * moore / 2))
    hi = min(moore // 2, MAX_N_SEARCH)
    N = lo
    while N <= hi and time.monotonic() < deadline:
        slice_end = min(deadline, time.monotonic() + SLICE)
        groups = _groups(N)
        if not groups:
            N += 1
            continue
        found = None
        while found is None and time.monotonic() < slice_end:
            m, k, r = rng.choice(groups)
            T, invs = _cached_table(m, k, r)
            found = _anneal_S(N, T, invs, d, D, rng, ANNEAL_ITERS, slice_end)
        if found is not None:
            T, _ = _cached_table(*rng.choice(groups)) if False else (None, None)
            # Rebuild edges with the table of the group that succeeded.
            # (The group is recorded by the loop above; recompute deterministically.)
            edges = _last_edges(N, found)
            if edges is not None:
                consider(2 * N, edges)
        N += 1


_last_group = {}


def _last_edges(N, S):
    key = _last_group.get(N)
    if key is None:
        return None
    T, _ = _cached_table(*key)
    return [(x, N + int(T[x, g])) for x in range(N) for g in S]


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d-1 (q capped at 40)."""
    for q in range(min(d - 1, 40), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if best[0] >= moore:
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if best[0] >= moore:
        return best

    rng = random.Random(seed * 1000003 + d * 131 + D)
    try:
        _search_with_records(d, D, moore, deadline, rng, best[0], consider)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


def _search_with_records(d, D, moore, deadline, rng, cur_n, consider):
    """Same sweep as _search, but records which group produced each success."""
    lo = max(d, cur_n // 2 + 1, int(0.45 * moore / 2))
    hi = min(moore // 2, MAX_N_SEARCH)
    N = lo
    while N <= hi and time.monotonic() < deadline:
        slice_end = min(deadline, time.monotonic() + SLICE)
        groups = _groups(N)
        if not groups:
            N += 1
            continue
        found = None
        found_group = None
        while found is None and time.monotonic() < slice_end:
            g = rng.choice(groups)
            m, k, r = g
            T, invs = _cached_table(m, k, r)
            found = _anneal_S(N, T, invs, d, D, rng, ANNEAL_ITERS, slice_end)
            if found is not None:
                found_group = g
        if found is not None:
            m, k, r = found_group
            T, _ = _cached_table(m, k, r)
            edges = [(x, N + int(T[x, g])) for x in range(N) for g in found]
            consider(2 * N, edges)
        N += 1
