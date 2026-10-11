import math
import random
import time

import numpy as np

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k, element (a, b) coded as a*k + b.

    M[x, y] = x*y, with (a, b)(c, e) = (a + r^b c, b + e). Identity is code 0.
    """
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    powers = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    return M


def _pick_r(m, k, rng):
    """Pick an action r with r^k = 1 mod m and gcd(r, m) = 1; fall back to the trivial action r = 1."""
    if k == 1 or m < 3:
        return 1
    if k == 2 and rng.random() < 0.3:
        return m - 1  # dihedral-type action
    for _ in range(60):
        r = rng.randrange(2, m)
        if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
            return r
    return 1


def _cost(N, M, inv, S, D):
    """Number of unreached (source, vertex) pairs for the Haar graph H(G, S).

    Vertices are A_g = g and B_h = N + h, with A_g ~ B_{g*s} for s in S. Left
    multiplication is an automorphism, so BFS from A_e and from B_e covers all
    pairs. Cost 0 means diameter <= D.
    """
    RS = M[:, S]            # RS[x, j] = x * s_j      (A -> B step)
    LS = M[:, inv[S]]       # LS[h, j] = h * s_j^{-1}  (B -> A step)
    total = 0
    for side in (0, 1):
        VA = np.zeros(N, dtype=bool)
        VB = np.zeros(N, dtype=bool)
        if side == 0:
            VA[0] = True
        else:
            VB[0] = True
        front = np.array([0], dtype=np.int64)
        on_a = (side == 0)
        for _ in range(D):
            m = np.zeros(N, dtype=bool)
            if on_a:
                m[RS[front].ravel()] = True
                m &= ~VB
                VB |= m
            else:
                m[LS[front].ravel()] = True
                m &= ~VA
                VA |= m
            front = np.flatnonzero(m)
            if front.size == 0:
                break
            on_a = not on_a
        total += 2 * N - int(VA.sum()) - int(VB.sum())
    return total


def _anneal(N, M, inv, d, D, rng, end, iters):
    """Annealing over connection sets S of size d. Returns S (cost 0) or None."""
    S = rng.sample(range(N), d)
    cost = _cost(N, M, inv, np.array(S, dtype=np.int64), D)
    for t in range(iters):
        if cost == 0:
            return S
        if time.monotonic() > end:
            break
        i = rng.randrange(d)
        members = set(S)
        x = rng.randrange(N)
        while x in members:
            x = rng.randrange(N)
        S2 = S.copy()
        S2[i] = x
        c2 = _cost(N, M, inv, np.array(S2, dtype=np.int64), D)
        T = 0.3 + 2.0 * (1.0 - t / iters)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            S, cost = S2, c2
    return S if cost == 0 else None


def _attempt(N, d, D, rng, end):
    """Try groups of order N with random restarts until end. Returns (S, m, k, r) or None."""
    ks = [k for k in range(1, min(N, 16) + 1) if N % k == 0 and N // k >= 2]
    if not ks:
        return None
    while time.monotonic() < end:
        k = rng.choice(ks)
        m = N // k
        r = _pick_r(m, k, rng)
        M = _table(m, k, r)
        inv = np.nonzero(M == 0)[1]
        S = _anneal(N, M, inv, d, D, rng, end, 1500)
        if S is not None:
            return (S, m, k, r)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    if D == 2 or d < 2:
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best_n and lib.is_valid(pg[0], pg[1], d, D):
            best, best_n = pg, pg[0]
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    successes = []
    try:
        N = max(d + 1, best_n // 2 + 1)
        fails = 0
        while time.monotonic() < deadline and fails < 4 and N <= 1500:
            slice_end = min(deadline, time.monotonic() + 2.5)
            res = _attempt(N, d, D, rng, slice_end)
            if res is not None:
                successes.append((N,) + res)
                fails = 0
            else:
                fails += 1
            N += 1
    except Exception:
        pass

    try:
        for (N, S, m, k, r) in sorted(successes, key=lambda t: t[0], reverse=True)[:4]:
            if 2 * N <= best_n:
                break
            M = _table(m, k, r)
            edges = [(g, N + int(M[g, s])) for g in range(N) for s in S]
            if lib.is_valid(2 * N, edges, d, D):
                best = (2 * N, edges)
                best_n = 2 * N
                break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
