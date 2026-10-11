import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# D = 3: projective planes (and the Araujo-Pardo--Lopez extension) as baselines.
# D >= 4: bi-Cayley lifts over semidirect products Z_m x|_r Z_k, searched with a
# numpy ball-growth cost and annealing-style acceptance, sweeping orders N just
# above the current best. Every candidate is verified by lib.is_valid.
# ----------------------------------------------------------------------------

N_WINDOW = 8        # candidate orders N above the current lower bound
MAX_GROUPS = 12     # groups tried per order N
CLIMB_ITERS = 4000  # search steps per restart
STALL_LIMIT = 400   # restart after this many non-improving steps
UPHILL_P = 0.02     # probability of accepting a worsening move
_GROUP_CACHE = {}


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


def _group_tables(m, k, r):
    """Return (N, TT, TI): TT[g][x] = x*g and TI[g][x] = x*g^-1, as int64 arrays."""
    key = (m, k, r)
    hit = _GROUP_CACHE.get(key)
    if hit is not None:
        return hit
    N, mul, inv = lib.semidirect_group(m, k, r)
    table = np.array([[mul(x, g) for g in range(N)] for x in range(N)], dtype=np.int64)
    TT = np.ascontiguousarray(table.T)                     # TT[g, x] = x*g
    invs = np.array([inv(g) for g in range(N)], dtype=np.int64)
    TI = np.ascontiguousarray(TT[invs])                    # TI[g, x] = x*g^-1
    val = (N, TT, TI)
    if len(_GROUP_CACHE) >= 64:
        _GROUP_CACHE.clear()
    _GROUP_CACHE[key] = val
    return val


def _unreached(N, TT, TI, S, D):
    """Number of (source, vertex) pairs at distance > D, sources A_0 and B_0.

    Bi-Cayley graph: A_x ~ B_{x g} for g in S. Left translation is an
    automorphism preserving both sides, so two sources suffice.
    """
    total = 0
    for side in (0, 1):
        XA = np.zeros(N, dtype=bool)
        XB = np.zeros(N, dtype=bool)
        if side == 0:
            XA[0] = True
        else:
            XB[0] = True
        size = 1
        for _ in range(D):
            NA = XA.copy()
            NB = XB.copy()
            for g in S:
                NB[TT[g]] |= XA
                NA[TI[g]] |= XB
            XA, XB = NA, NB
            new_size = int(XA.sum()) + int(XB.sum())
            if new_size == size:
                break
            size = new_size
        total += 2 * N - int(XA.sum()) - int(XB.sum())
    return total


def _climb(N, TT, TI, d, D, rng, iters, deadline):
    """Search a connection set S containing the identity to zero unreached pairs."""

    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, _unreached(N, TT, TI, S, D)

    S, cur = fresh()
    stall = 0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, TT, TI, S2, D)
        if v < cur:
            stall = 0
        else:
            stall += 1
        if v <= cur or rng.random() < UPHILL_P:
            S, cur = S2, v
        if stall > STALL_LIMIT:
            S, cur = fresh()
            stall = 0
    return S if cur == 0 else None


def _search_bicayley(d, D, N, rng, deadline):
    """Try several groups of order N; return (N, TT, S) for a valid lift, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        _, TT, TI = _group_tables(m, k, r)
        S = _climb(N, TT, TI, d, D, rng, CLIMB_ITERS, deadline)
        if S is not None:
            return N, TT, S
    return None


def _pg_candidates(d):
    """Baseline D = 3 graphs: PG(2, q) for the largest prime power q <= d - 1."""
    out = []
    q = max((x for x in range(2, d) if lib.is_prime_power(x)), default=None)
    if q is not None:
        out.append(lib.projective_plane_incidence(q))
    if d >= 5 and lib.is_prime_power(d - 2) and d - 2 >= 3:
        try:
            out.append(lib.araujo_lopez_graph(d - 2))
        except ValueError:
            pass
    return out


def _run(d, D, seed, deadline, best, consider):
    """Fill `best` through `consider`. Assumes d >= 2 and D >= 3."""
    rng = random.Random(seed)
    moore = lib._moore_bound(d, D)

    if D == 3:
        for n, e in _pg_candidates(d):
            consider(n, e)
        return

    while best[0] < moore and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(N_WINDOW)
        res = _search_bicayley(d, D, N, rng, deadline)
        if res is not None:
            Nf, TT, S = res
            edges = [(x, Nf + int(TT[g][x])) for g in S for x in range(Nf)]
            consider(2 * Nf, edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))   # K_{d,d}, diameter 2
    if D == 2 or d == 1:
        return fallback

    best = [fallback[0], fallback[1]]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    try:
        _run(d, D, seed, deadline, best, consider)
    except Exception:
        pass

    n, e = best
    if lib.is_valid(n, e, d, D):
        return n, e
    return fallback
