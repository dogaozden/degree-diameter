import math
import random
import time

import numpy as np

import lib


MAX_GROUPS = 10      # groups tried per order before resampling the order
ANNEAL_ITERS = 1500  # annealing steps per group
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# Structured baseline for D = 3: incidence graph of PG(2, q).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k, scored with numpy boolean BFS.
#
# Vertices: A_x and B_z for x, z in the group G. Edge A_x ~ B_{x*s} for s in S.
# Left translation is an automorphism, so the eccentricities of A_0 and B_0
# determine the diameter.
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


def _table(m, k, r):
    """Cached (G, T, Ginv): T[g, x] = x*g and Ginv[g] = g^-1, as numpy arrays."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = np.array([[mul(x, g) for x in range(order)] for g in range(order)], dtype=np.int64)
    Ginv = np.array([inv(g) for g in range(order)], dtype=np.int64)
    val = (order, T, Ginv)
    if len(_TABLE_CACHE) >= 64:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(G, T, Ginv, S, D):
    """Number of (source, vertex) pairs not within distance D, sources A_0 and B_0."""
    TS = T[S]              # TS[i, x] = x * s_i        (A -> B)
    TSi = T[Ginv[S]]       # TSi[i, z] = z * s_i^-1    (B -> A)
    total = 0
    for side in (0, 1):
        sa = np.zeros(G, dtype=bool)
        sb = np.zeros(G, dtype=bool)
        fa = np.zeros(G, dtype=bool)
        fb = np.zeros(G, dtype=bool)
        if side == 0:
            sa[0] = True
            fa[0] = True
        else:
            sb[0] = True
            fb[0] = True
        for _ in range(D):
            if not (fa.any() or fb.any()):
                break
            nb = np.zeros(G, dtype=bool)
            xs = np.flatnonzero(fa)
            if xs.size:
                nb[TS[:, xs].ravel()] = True
            na = np.zeros(G, dtype=bool)
            zs = np.flatnonzero(fb)
            if zs.size:
                na[TSi[:, zs].ravel()] = True
            nb &= ~sb
            na &= ~sa
            sb |= nb
            sa |= na
            fa, fb = na, nb
        total += 2 * G - int(sa.sum()) - int(sb.sum())
    return total


def _anneal_S(G, T, Ginv, d, D, rng, deadline, iters):
    """Annealing over a d-element connection set containing the identity (WLOG).

    Returns S (numpy array) with zero unreached pairs, or None.
    """
    if d - 1 > G - 1:
        return None
    S = np.array([0] + rng.sample(range(1, G), d - 1), dtype=np.int64)
    cur = _unreached(G, T, Ginv, S, D)
    T0 = 2.0 + 0.1 * cur
    for step in range(iters):
        if cur == 0:
            return S
        if (step & 15) == 0 and time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.15
        i = rng.randrange(1, d)
        c = rng.randrange(1, G)
        if c in S.tolist():
            continue
        old = int(S[i])
        S[i] = c
        v = _unreached(G, T, Ginv, S, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = v
        else:
            S[i] = old
    return S if cur == 0 else None


def _bicayley_edges(G, T, S):
    """Edges of the bi-Cayley graph: A_x (index x) ~ B_{x*s} (index G + x*s)."""
    edges = []
    for s in S.tolist():
        for x in range(G):
            edges.append((x, G + int(T[s, x])))
    return edges


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, always valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d < 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if best[0] >= moore:
            return best

    # Main search: bi-Cayley lifts with numpy-scored annealing. Each attempt
    # targets an order just above the current best, so the best only rises.
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = n_best // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(max(2, lo // 12))
        groups = _groups(N)
        if not groups:
            continue
        rng.shuffle(groups)
        for m, k, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            G, T, Ginv = _table(m, k, r)
            S = _anneal_S(G, T, Ginv, d, D, rng, deadline, ANNEAL_ITERS)
            if S is not None:
                consider(2 * G, _bicayley_edges(G, T, S))
                if best[0] > n_best:
                    break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
