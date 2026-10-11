import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Strategy: bi-Cayley lifts over semidirect products Z_m x|_r Z_k.
#
# A group G of order N with connection set S (|S| = d, identity in S WLOG)
# gives the bipartite graph A_x ~ B_{x*g} for g in S, with 2N vertices, degree d.
# Left translations are automorphisms, so the diameter condition reduces to
# eccentricities of A_0 and B_0.
#
# Evaluation is vectorised with numpy boolean frontiers (R[g, x] = x*g). Search
# is simulated annealing on S, with the count of unreached pairs as the cost.
# Orders N are swept upward from the best order found so far.
#
# Safe fallbacks: K_{d,d} (diameter 2), the projective plane incidence graph
# for D = 3 with d-1 a prime power, and the even cycle for d = 2. Every
# returned graph passes lib.is_valid.
# ----------------------------------------------------------------------------

WINDOW = 3          # candidate orders above the current best
MAX_GROUPS = 6      # groups tried per order
ITERS = 2000        # annealing steps per climb
STALL = 350         # restart a climb after this many non-improving steps
TEMP = 0.7          # annealing temperature (in unreached-pair units)
_BIG = 10 ** 12
_TAB = {}


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
    """Cached (R, ginv): R[g, x] = x*g as an int array, ginv[g] = g^-1."""
    key = (m, k, r)
    hit = _TAB.get(key)
    if hit is not None:
        return hit
    N, mul, inv = lib.semidirect_group(m, k, r)
    R = np.array([[mul(x, g) for x in range(N)] for g in range(N)], dtype=np.int64)
    ginv = [inv(g) for g in range(N)]
    val = (R, ginv)
    if len(_TAB) >= 40:
        _TAB.clear()
    _TAB[key] = val
    return val


def _cost(N, Rg, Rinv, D, limit):
    """Unreached (source, vertex) pairs from A_0 and B_0 within distance D.

    Returns early with a value above `limit` once the running total exceeds it.
    """
    total = 0
    for side in (0, 1):
        seenA = np.zeros(N, dtype=bool)
        seenB = np.zeros(N, dtype=bool)
        if side == 0:
            seenA[0] = True
            onA = True
        else:
            seenB[0] = True
            onA = False
        front = np.array([0], dtype=np.int64)
        for _ in range(D):
            if front.size == 0:
                break
            nxt = np.zeros(N, dtype=bool)
            if onA:
                for r in Rg:
                    nxt[r[front]] = True
                nxt &= ~seenB
                seenB |= nxt
            else:
                for r in Rinv:
                    nxt[r[front]] = True
                nxt &= ~seenA
                seenA |= nxt
            front = np.flatnonzero(nxt)
            onA = not onA
        total += 2 * N - int(seenA.sum()) - int(seenB.sum())
        if total > limit:
            return total
    return total


def _climb(N, R, ginv, d, D, rng, iters, deadline):
    """Annealed search for S (|S| = d, 0 in S) with zero unreached pairs."""
    def rows(S):
        return [R[g] for g in S], [R[ginv[g]] for g in S]

    def fresh():
        return [0] + rng.sample(range(1, N), d - 1)

    S = fresh()
    rg, ri = rows(S)
    cur = _cost(N, rg, ri, D, _BIG)
    stall = 0
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        rg2, ri2 = rows(S2)
        # Accept iff v - cur <= -TEMP*ln(u) for a fresh uniform u (Metropolis rule).
        u = rng.random() + 1e-12
        lim = cur - TEMP * math.log(u)
        v = _cost(N, rg2, ri2, D, lim)
        if v < cur:
            stall = 0
        else:
            stall += 1
        if v <= lim:
            S, cur, rg, ri = S2, v, rg2, ri2
        if stall > STALL:
            S = fresh()
            rg, ri = rows(S)
            cur = _cost(N, rg, ri, D, _BIG)
            stall = 0
    return S if cur == 0 else None


def _search_N(d, D, N, rng, deadline):
    """Try several groups of order N; return a valid connection set S or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        R, ginv = _table(m, k, r)
        S = _climb(N, R, ginv, d, D, rng, ITERS, deadline)
        if S is not None:
            return R, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.2, min(0.8 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
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

    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    # Bi-Cayley sweep: each success raises the order N.
    half = moore // 2
    best_N = best[0] // 2
    while time.monotonic() < deadline and best_N < half:
        N = best_N + 1 + rng.randrange(WINDOW)
        if N > half:
            N = best_N + 1
        if N > half or N < d:
            break
        res = _search_N(d, D, N, rng, deadline)
        if res is None:
            continue
        R, S = res
        edges = [(x, N + int(R[g][x])) for x in range(N) for g in S]
        if lib.is_valid(2 * N, edges, d, D):
            best = (2 * N, edges)
            best_N = N

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
