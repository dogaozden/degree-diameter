import math
import random
import time

import numpy as np

import lib

MAX_GROUPS = 6     # groups tried per order N before moving on
ITERS = 1500       # annealing steps per (N, group)
WINDOW = 40        # search orders N in [lo, lo + WINDOW]


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _right_table(m, k, r):
    """T[x, g] = x * g for the group Z_m x|_r Z_k, element (a, b) coded as a*k + b."""
    N = m * k
    idx = np.arange(N, dtype=np.int64)
    A = idx // k
    B = idx % k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    a = A[:, None]
    b = B[:, None]
    c = A[None, :]
    dd = B[None, :]
    newA = (a + pw[b] * c) % m
    newB = (b + dd) % k
    return (newA * k + newB).astype(np.int64)


def _reach(T, Sarr, Sinv, N, D, side):
    """Number of vertices within distance D of source A_0 (side 0) or B_0 (side 1).

    Bi-Cayley graph: A_x ~ B_{x g} for g in S. The left action is an automorphism,
    so eccentricities of A_0 and B_0 determine the diameter.
    """
    seenA = np.zeros(N, dtype=bool)
    seenB = np.zeros(N, dtype=bool)
    front = np.zeros(1, dtype=np.intp)
    if side == 0:
        seenA[0] = True
        on_a = True
    else:
        seenB[0] = True
        on_a = False
    for _ in range(D):
        if front.size == 0:
            break
        mask = np.zeros(N, dtype=bool)
        if on_a:
            mask[T[np.ix_(front, Sarr)].ravel()] = True
            new = mask & ~seenB
            seenB |= new
        else:
            mask[T[np.ix_(front, Sinv)].ravel()] = True
            new = mask & ~seenA
            seenA |= new
        front = np.flatnonzero(new)
        on_a = not on_a
    return int(seenA.sum()) + int(seenB.sum())


def _cost(T, invs, S, N, D):
    """Unreached (source, vertex) pairs from A_0 and B_0. Zero means diameter <= D."""
    Sarr = np.array(S, dtype=np.int64)
    Sinv = invs[Sarr]
    reached = _reach(T, Sarr, Sinv, N, D, 0) + _reach(T, Sarr, Sinv, N, D, 1)
    return 4 * N - reached


def _anneal(T, invs, N, d, D, rng, iters, deadline):
    """Simulated annealing over connection sets S (identity fixed as one element)."""
    if N < d:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _cost(T, invs, S, N, D)
    best_cost, best_S = cur, list(S)
    T0 = 1.0 + 0.05 * cur
    for step in range(iters):
        if best_cost == 0:
            break
        if (step & 127) == 0 and time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.1
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = _cost(T, invs, S, N, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / temp)):
            cur = v
            if cur < best_cost:
                best_cost, best_S = cur, list(S)
        else:
            S[i] = old
    return best_S if best_cost == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

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

    # Main search: bi-Cayley lifts over semidirect products, annealed with
    # bit-parallel-style numpy BFS. Each success raises the order target.
    tried = {}
    try:
        while best[0] < moore and time.monotonic() < deadline:
            lo = best[0] // 2 + 1
            hi = min(moore // 2, lo + WINDOW)
            cands = list(range(max(lo, d), hi + 1))
            if not cands:
                break
            N = min(cands, key=lambda x: (tried.get(x, 0), rng.random()))
            tried[N] = tried.get(N, 0) + 1

            groups = _groups(N)
            rng.shuffle(groups)
            found = None
            for m, k, r in groups[:MAX_GROUPS]:
                if time.monotonic() > deadline:
                    break
                T = _right_table(m, k, r)
                invs = np.argmax(T == 0, axis=1)
                S = _anneal(T, invs, N, d, D, rng, ITERS, deadline)
                if S is not None:
                    found = (T, S)
                    break
            if found is not None:
                T, S = found
                edges = [(x, N + int(T[x, g])) for x in range(N) for g in S]
                consider(2 * N, edges)
    except Exception:
        pass  # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
