import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# D = 3: projective plane incidence graphs (PG(2, q), q + 1 <= d).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x|_r Z_k.
#
# The graph has parts A_x and B_y (x, y in G), with A_x ~ B_{x*g} for g in S,
# |S| = d. Left translation is an automorphism preserving both parts, so the
# diameter check only needs BFS from A_0 and from B_0.
#
# The search is simulated annealing over S with a numpy-vectorised BFS cost
# (number of ordered (source, target) pairs at distance > D).
# ----------------------------------------------------------------------------

MAX_GROUPS = 12
ANNEAL_ITERS = 2500
_CACHE = {}


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
    """Cached (order, T, invs): T[x, g] = x*g as a numpy table, invs[g] = g^-1."""
    key = (m, k, r)
    hit = _CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = np.array([[mul(x, g) for g in range(order)] for x in range(order)], dtype=np.int64)
    invs = np.array([inv(g) for g in range(order)], dtype=np.int64)
    if len(_CACHE) >= 64:
        _CACHE.clear()
    val = (order, T, invs)
    _CACHE[key] = val
    return val


def _unreached(N, Fwd, Bwd, D):
    """Ordered (source, target) pairs not within distance D, sources A_0 and B_0.

    Fwd[x, j] is the B-index adjacent to A_x via the j-th element of S.
    Bwd[y, j] is the A-index adjacent to B_y via the j-th element of S.
    """
    total = 0
    for side in (0, 1):
        seen = [np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)]
        seen[side][0] = True
        frontier = np.array([0], dtype=np.int64)
        cur = side
        count = 1
        for _ in range(D):
            nb = (Fwd if cur == 0 else Bwd)[frontier].ravel()
            tgt = 1 - cur
            mask = np.zeros(N, dtype=bool)
            mask[nb] = True
            mask &= ~seen[tgt]
            seen[tgt] |= mask
            frontier = np.flatnonzero(mask)
            cur = tgt
            count += frontier.size
            if frontier.size == 0:
                break
        total += 2 * N - count
    return total


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    """Anneal a connection set S (identity fixed as element 0, WLOG).

    Returns a valid S (zero unreached pairs) or None.
    """
    def ev(S):
        Sa = np.array(S, dtype=np.int64)
        return _unreached(N, T[:, Sa], T[:, invs[Sa]], D)

    S = [0] + rng.sample(range(1, N), d - 1)
    cur = ev(S)
    best_v, best_S = cur, S[:]
    T0 = 3.0 + 0.1 * cur
    for step in range(iters):
        if best_v == 0 or time.monotonic() > deadline:
            break
        temp = 0.3 + (T0 - 0.3) * (1.0 - step / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = ev(S2)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur < best_v:
                best_v, best_S = cur, S[:]
    return best_S if best_v == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every d >= 1.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if best[0] >= moore or d < 2:
        return best

    rng = random.Random(seed * 1000003 + d * 31 + D)
    target = best[0] // 2 + 1
    max_N = moore // 2

    try:
        while time.monotonic() < deadline and target <= max_N:
            N = min(max_N, target + rng.randrange(0, 3))
            N = max(N, d + 1)
            if N > max_N:
                break
            groups = _groups(N)
            rng.shuffle(groups)
            found = None
            for m, k, r in groups[:MAX_GROUPS]:
                if time.monotonic() >= deadline:
                    break
                order, T, invs = _tables(m, k, r)
                S = _anneal(order, T, invs, d, D, rng, ANNEAL_ITERS, deadline)
                if S is not None:
                    found = (order, T, S)
                    break
            if found is not None:
                order, T, S = found
                Tl = T.tolist()
                edges = [(x, order + Tl[x][g]) for x in range(order) for g in S]
                consider(2 * order, edges)
                target = max(target, order + 1)
    except Exception:
        pass  # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
