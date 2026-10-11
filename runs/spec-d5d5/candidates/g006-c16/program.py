import math
import random
import time

import numpy as np

import lib

# Bold change: instead of the list-based BFS used by the parent, every bi-Cayley
# candidate is scored with vectorised numpy BFS on the whole group at once. That
# gives an order of magnitude more candidate evaluations per second. The search
# then sweeps group orders N upward from the current best (2N vertices), using a
# per-order time budget and random group sampling. Every returned graph is
# checked with lib.is_valid, and K_{d,d} is the fallback.

MAX_GROUPS = 6        # semidirect groups tried per order N
CLIMB_ITERS = 1200    # hill-climb steps per group
STALL_LIMIT = 250     # re-randomise the connection set after this many non-improving steps
PER_N_SECONDS = 1.0   # time budget per group order N
_TABLE_CACHE = {}


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


def _tables(m, k, r):
    """Cached (T, invs): T[x, g] = x*g as a numpy table, invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    N = m * k
    X = np.arange(N, dtype=np.int64)
    a = X // k
    b = X % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    # (a, b) * (c, d) = (a + r^b c, b + d)
    T = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    nb = (-b) % k
    invs = ((-pw[nb] * a) % m) * k + nb
    val = (T, invs)
    if len(_TABLE_CACHE) >= 24:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Number of vertex pairs (source, target) not within distance D, from A_0 and B_0.

    Bi-Cayley graph: A_x ~ B_{x g} for g in S. Left translations act transitively on
    each side, so checking the two sources is enough for the whole graph.
    """
    Sarr = np.asarray(S, dtype=np.int64)
    Sinv = invs[Sarr]
    total = 0
    for start_side in (0, 1):
        ra = np.zeros(N, dtype=bool)
        rb = np.zeros(N, dtype=bool)
        fr = np.zeros(1, dtype=np.int64)
        if start_side == 0:
            ra[0] = True
        else:
            rb[0] = True
        side = start_side
        for _ in range(D):
            new = np.zeros(N, dtype=bool)
            if side == 0:
                new[T[np.ix_(fr, Sarr)]] = True
                new &= ~rb
                rb |= new
            else:
                new[T[np.ix_(fr, Sinv)]] = True
                new &= ~ra
                ra |= new
            fr = np.flatnonzero(new)
            side ^= 1
            if fr.size == 0:
                break
        total += 2 * N - int(ra.sum()) - int(rb.sum())
    return total


def _climb(N, T, invs, d, D, rng, deadline):
    """Hill-climb a connection set S (identity fixed as one element) to zero unreached pairs."""
    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, _unreached(N, T, invs, S, D)

    S, cur = fresh()
    stall = 0
    for it in range(CLIMB_ITERS):
        if cur == 0:
            return S
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v < cur:
            stall = 0
        else:
            stall += 1
        if v <= cur:
            S, cur = S2, v
        if stall > STALL_LIMIT:
            S, cur = fresh()
            stall = 0
    return S if cur == 0 else None


def _search_N(N, d, D, rng, deadline):
    """Try several semidirect groups of order N; return (T, S) for a valid lift, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        T, invs = _tables(m, k, r)
        S = _climb(N, T, invs, d, D, rng, deadline)
        if S is not None:
            return T, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and order 2d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # D = 3: projective plane incidence graph for the largest prime power q with q + 1 <= d.
    if D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if qs:
            consider(*lib.projective_plane_incidence(qs[0]))
        if best[0] >= moore:
            return best

    # Main search: bi-Cayley lifts with N sweeping upward from the current best.
    if d >= 2:
        hi = moore // 2
        N = max(best[0] // 2 + 1, d + 1)
        while N <= hi and time.monotonic() < deadline:
            per = min(deadline, time.monotonic() + PER_N_SECONDS)
            res = _search_N(N, d, D, rng, per)
            if res is not None:
                T, S = res
                Sarr = np.asarray(S, dtype=np.int64)
                edges = [(x, N + int(y)) for x in range(N) for y in T[x, Sarr]]
                consider(2 * N, edges)
            N = max(N + 1, best[0] // 2 + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
