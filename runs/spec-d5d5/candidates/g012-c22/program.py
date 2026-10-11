import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# D = 3 baseline: incidence graph of PG(2, q) for the largest usable q.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Vectorized bi-Cayley lifts over Z_m x|_r Z_k.
#
# Vertices: A_x = x and B_y = N + y, with x, y in G (|G| = N).
# Connection set S (with 0 in S, WLOG): A_x ~ B_{x*g} for g in S.
# Left multiplication is an automorphism, so eccentricities from A_0 and B_0
# decide the diameter of the whole graph.
#
# New helper here: a numpy table of the group multiplication (built with
# array arithmetic instead of Python loops) and a layered two-source BFS on
# boolean masks. Each annealing step then costs a few numpy calls.
# ----------------------------------------------------------------------------

_CACHE = {}


def _semidirect_np(m, k, r):
    """Return (N, T, inv) with T[x, g] = x*g and inv[g] = g^-1 for Z_m x|_r Z_k (element (a, b) = a*k + b)."""
    N = m * k
    X = np.arange(N, dtype=np.int64)
    a = X // k
    b = X % k
    P = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64) % m
    A = a[:, None]
    B = b[:, None]
    C = a[None, :]
    Dd = b[None, :]
    T = ((A + P[B] * C) % m) * k + (B + Dd) % k
    nb = (-b) % k
    inv = ((-P[nb] * a) % m) * k + nb
    return N, T.astype(np.int64), inv.astype(np.int64)


def _tables(m, k, r):
    """Cached (N, T, inv) for a semidirect group."""
    key = (m, k, r)
    hit = _CACHE.get(key)
    if hit is not None:
        return hit
    if len(_CACHE) > 64:
        _CACHE.clear()
    val = _semidirect_np(m, k, r)
    _CACHE[key] = val
    return val


def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N and r^k = 1 mod m, gcd(r, m) = 1."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _defect(N, TS, TI, D):
    """Total number of (source, vertex) pairs not within distance D, sources A_0 and B_0.

    TS[x, j] = neighbour index of A_x via S_j (on the B side);
    TI[y, j] = neighbour index of B_y via S_j (on the A side).
    """
    total = 0
    for start_side in (0, 1):
        vis = [np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)]
        vis[start_side][0] = True
        front = np.zeros(1, dtype=np.int64)
        side = start_side
        for _ in range(D):
            M = TS if side == 0 else TI
            cand = M[front].ravel()
            mask = np.zeros(N, dtype=bool)
            mask[cand] = True
            mask &= ~vis[1 - side]
            new = np.flatnonzero(mask)
            vis[1 - side][new] = True
            front = new
            side = 1 - side
            if front.size == 0:
                break
        total += 2 * N - int(vis[0].sum()) - int(vis[1].sum())
    return total


def _anneal_S(N, T, inv, d, D, rng, deadline, iters):
    """Anneal a connection set S (0 fixed, |S| = d) to zero defect; return S or None."""
    S = [0] + rng.sample(range(1, N), d - 1)

    def cost(SS):
        arr = np.array(SS, dtype=np.int64)
        return _defect(N, T[:, arr], T[:, inv[arr]], D)

    cur = cost(S)
    for it in range(iters):
        if cur == 0:
            break
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = cost(S2)
        temp = 2.0 * (1.0 - it / iters) + 0.2
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

MAX_GROUPS = 6     # groups tried per order N before moving on
ANNEAL_ITERS = 1500


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2 and order 2d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
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

    # Bi-Cayley search: sweep the group order N upward, aiming for 2N > best.
    N = best[0] // 2 + 1
    while time.monotonic() < deadline and best[0] < moore and N <= moore // 2:
        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for m, k, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            Nn, T, inv = _tables(m, k, r)
            S = _anneal_S(Nn, T, inv, d, D, rng, deadline, ANNEAL_ITERS)
            if S is not None:
                found = (T, S)
                break
        if found is not None:
            T, S = found
            Tl = T.tolist()
            edges = [(x, N + Tl[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
