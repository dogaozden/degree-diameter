import math
import random
import time

import numpy as np

import lib

# Bi-Cayley lifts over semidirect products Z_m x|_r Z_k.
#
# Vertices A_x and B_x for x in G (|G| = N). A_x ~ B_{x g} for g in S, |S| = d.
# Left translation is an automorphism, so only eccentricities of A_0 and B_0
# need checking. Distance evaluation is vectorised with numpy, and a
# simulated-annealing-style climb searches over connection sets S.
# Every candidate is re-verified with lib.is_valid before it is accepted.

MAX_GROUPS = 8
CLIMB_ITERS = 400
N_CAP = 1200
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


def _table(m, k, r):
    """Cached (N, T, invs): T[x, g] = x*g and invs[g] = g^-1 as numpy arrays."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    A = a[:, None]
    B = b[:, None]
    C = a[None, :]
    Dd = b[None, :]
    T = ((A + pw[B] * C) % m) * k + (B + Dd) % k
    nb = (-b) % k
    invs = ((-pw[nb] * a) % m) * k + nb
    val = (N, T, invs)
    if len(_TABLE_CACHE) > 32:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Number of (source, target) pairs not within distance D, from A_0 and from B_0."""
    Sinv = [int(invs[g]) for g in S]
    total = 0
    for side in (0, 1):
        seenA = np.zeros(N, dtype=bool)
        seenB = np.zeros(N, dtype=bool)
        fa = np.zeros(N, dtype=bool)
        fb = np.zeros(N, dtype=bool)
        if side == 0:
            fa[0] = True
            seenA[0] = True
        else:
            fb[0] = True
            seenB[0] = True
        count = 1
        for _ in range(D):
            ia = np.flatnonzero(fa)
            ib = np.flatnonzero(fb)
            nb = np.zeros(N, dtype=bool)
            na = np.zeros(N, dtype=bool)
            if ia.size:
                for g in S:
                    nb[T[ia, g]] = True
            if ib.size:
                for h in Sinv:
                    na[T[ib, h]] = True
            nb &= ~seenB
            na &= ~seenA
            seenB |= nb
            seenA |= na
            c = int(nb.sum()) + int(na.sum())
            count += c
            fa, fb = na, nb
            if c == 0:
                break
        total += 2 * N - count
    return total


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Search connection sets S (identity fixed WLOG) with zero unreached pairs.

    Sideways moves and occasional uphill moves (annealing-like) are accepted.
    """
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best_S, best_c = list(S), cur
    temp = 2.0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / max(temp, 1e-9)):
            S, cur = S2, v
            if cur < best_c:
                best_S, best_c = list(S), cur
        temp = max(0.05, temp * 0.99)
    return best_S if best_c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and max degree d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    # Structured baseline for D = 3: incidence graph of PG(2, d-1).
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Bi-Cayley search: a lift with N base elements has 2N vertices.
    N = best[0] // 2 + 1
    hi = min(moore // 2, N_CAP)
    while time.monotonic() < deadline and N <= hi:
        if N >= d:
            groups = _groups(N)
            rng.shuffle(groups)
            groups.sort(key=lambda t: t[1] == 1)  # non-abelian candidates first
            for m, k, r in groups[:MAX_GROUPS]:
                if time.monotonic() > deadline:
                    break
                _, T, invs = _table(m, k, r)
                S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
                if S is None:
                    continue
                edges = [(x, N + int(T[x, g])) for x in range(N) for g in S]
                if lib.is_valid(2 * N, edges, d, D):
                    best = (2 * N, edges)
                    break
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
