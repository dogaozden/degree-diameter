import math
import random
import time

import numpy as np

import lib

MAX_GROUPS = 8        # groups tried per order N
GREEDY_POOL = 24      # candidates sampled per greedy seeding step


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


def _prepare(N, m, k, r):
    """Multiplication table Tm[x, g] = x*g and inverse table for a group of order N."""
    _, mul, inv = lib.semidirect_group(m, k, r)
    Tm = np.array([[mul(x, g) for g in range(N)] for x in range(N)], dtype=np.int64)
    invs = np.array([inv(g) for g in range(N)], dtype=np.int64)
    return Tm, invs


def _cost(Tm, N, D, S, Sinv):
    """Vectorised count of unreached pairs for the bi-Cayley graph A_x ~ B_{x g}, g in S.

    Left translation is an automorphism acting transitively on A and on B,
    so BFS from A_0 and from B_0 gives the exact eccentricity profile.
    """
    total = 0
    for side0 in (0, 1):
        seen = (np.zeros(N, dtype=bool), np.zeros(N, dtype=bool))
        seen[side0][0] = True
        frontier = np.array([0], dtype=np.int64)
        side = side0
        count = 1
        for _ in range(D):
            if side == 0:
                tg = Tm[np.ix_(frontier, S)]      # A_x -> B_{x g}
            else:
                tg = Tm[np.ix_(frontier, Sinv)]   # B_w -> A_{w g^-1}
            t = np.unique(tg)
            t = t[~seen[1 - side][t]]
            if t.size == 0:
                break
            seen[1 - side][t] = True
            count += int(t.size)
            frontier = t
            side = 1 - side
        total += 2 * N - count
    return total


def _anneal(Tm, invs, N, d, D, rng, deadline):
    """Find a connection set S of size d with zero unreached pairs.

    New here: greedy seeding (each new dart chosen as the best of a random
    sample, measured by unreached pairs), then simulated annealing with a
    temperature that cools linearly to the deadline.
    """
    def ev(S):
        Sa = np.array(S, dtype=np.int64)
        return _cost(Tm, N, D, Sa, invs[Sa])

    S = [0]
    while len(S) < d:
        pool = [c for c in range(1, N) if c not in S]
        cand = rng.sample(pool, min(GREEDY_POOL, len(pool)))
        best_c, best_v = None, None
        for c in cand:
            v = ev(S + [c])
            if best_v is None or v < best_v:
                best_c, best_v = c, v
        S.append(best_c)

    cur = ev(S)
    best, bestS = cur, S[:]
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        temp = 0.2 + 2.0 * max(0.0, 1.0 - (now - t0) / span)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = ev(S2)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
            if cur < best:
                best, bestS = cur, S[:]
    return bestS if best == 0 else None


def _try_N(N, d, D, rng, deadline):
    """Try to build a valid bi-Cayley graph on 2N vertices before the deadline; return edges or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    groups = groups[:MAX_GROUPS]
    for idx, (m, k, r) in enumerate(groups):
        now = time.monotonic()
        if now >= deadline:
            break
        left = len(groups) - idx
        sub = now + (deadline - now) / left
        Tm, invs = _prepare(N, m, k, r)
        S = _anneal(Tm, invs, N, d, D, rng, sub)
        if S is not None:
            edges = [(x, N + int(Tm[x, g])) for x in range(N) for g in S]
            if lib.is_valid(2 * N, edges, d, D):
                return edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard = start + max(1.0, min(0.85 * time_limit, time_limit - 6.0))

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if d < 2 or D < 2:
        return best

    rng = random.Random(seed)
    Nmax = lib._moore_bound(d, D) // 2

    # New: binary search over the half-order N (feasibility is roughly monotone),
    # so budget goes to plausible orders instead of sweeping every N upward.
    lo, hi = d + 1, min(Nmax, 215)
    while lo <= hi:
        now = time.monotonic()
        if now >= hard:
            break
        mid = (lo + hi + 1) // 2
        rem = hard - now
        budget = min(6.0, max(0.8, rem / 3.0))
        edges = _try_N(mid, d, D, rng, min(hard, now + budget))
        if edges is not None:
            if 2 * mid > best[0]:
                best = (2 * mid, edges)
            lo = mid + 1
        else:
            hi = mid - 1

    return best
