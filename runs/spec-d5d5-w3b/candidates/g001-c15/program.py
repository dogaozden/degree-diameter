import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Tunables
# ----------------------------------------------------------------------------

ITERS = 900            # annealing steps per (group, connection set) try
MAX_GROUPS = 8         # random groups tried per order N in one attempt
T_HOT = 1.2
T_COLD = 0.1
MAX_N_TABLE = 1200     # cap on group order (tables are N x N)


# ----------------------------------------------------------------------------
# Group construction: direct products of semidirect products Z_m x|_r Z_k.
# Elements are mixed-radix indices; multiplication tables are built vectorized.
# ----------------------------------------------------------------------------

def _divisors(n):
    return [f for f in range(1, n + 1) if n % f == 0]


def _semidirect_params(N):
    """All (m, k, r) with m*k = N and Z_m x|_r Z_k well defined."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _factor_tables(m, k, r):
    """(order, T, inv) for Z_m x|_r Z_k with element (a, b) coded a*k + b."""
    N = m * k
    r %= m
    xs = np.arange(N, dtype=np.int64)
    a = xs // k
    b = xs % k
    P = np.array([pow(r, bb, m) for bb in range(k)], dtype=np.int64)
    T = ((a[:, None] + P[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    nb = (-b) % k
    inv = ((-P[nb] * a) % m) * k + nb
    return N, T, inv


def _product_tables(desc):
    """(order, T, inv) for the direct product of the semidirect factors in desc."""
    facs = [_factor_tables(*f) for f in desc]
    sizes = [f[0] for f in facs]
    N = 1
    for s in sizes:
        N *= s
    strides = []
    st = 1
    for s in reversed(sizes):
        strides.append(st)
        st *= s
    strides.reverse()
    idx = np.arange(N, dtype=np.int64)
    T = np.zeros((N, N), dtype=np.int64)
    inv = np.zeros(N, dtype=np.int64)
    for (Ni, Ti, invi), stride in zip(facs, strides):
        dig = (idx // stride) % Ni
        T += Ti[dig[:, None], dig[None, :]] * stride
        inv += invi[dig] * stride
    return N, T, inv


def _random_group(N, rng):
    """Random factorization of N into semidirect factors (as a tuple of (m, k, r))."""
    desc = []
    rem = N
    while rem > 1:
        divs = [f for f in _divisors(rem) if f > 1]
        f = rem if rng.random() < 0.5 else rng.choice(divs)
        desc.append(rng.choice(_semidirect_params(f)))
        rem //= f
    if not desc:
        desc = [(1, 1, 0)]
    return tuple(desc)


# ----------------------------------------------------------------------------
# Bi-Cayley lifts: A_x ~ B_{x g} for g in S, |S| = d, 0 in S (WLOG).
# By left-translation symmetry, distances from A_0 and B_0 decide the diameter.
# ----------------------------------------------------------------------------

def _unreached(N, T, invs, S, D):
    """Number of (source, vertex) pairs at distance > D from A_0 and from B_0."""
    TS = T[:, S]              # TS[x]: B-indices adjacent to A_x
    TIS = T[:, invs[S]]       # TIS[y]: A-indices adjacent to B_y
    total = 0
    for side in (0, 1):
        seenA = np.zeros(N, dtype=bool)
        seenB = np.zeros(N, dtype=bool)
        if side == 0:
            seenA[0] = True
            fA = seenA.copy()
            fB = np.zeros(N, dtype=bool)
        else:
            seenB[0] = True
            fB = seenB.copy()
            fA = np.zeros(N, dtype=bool)
        for _ in range(D):
            if not (fA.any() or fB.any()):
                break
            nb = np.zeros(N, dtype=bool)
            nb[TS[fA].ravel()] = True
            na = np.zeros(N, dtype=bool)
            na[TIS[fB].ravel()] = True
            nb &= ~seenB
            na &= ~seenA
            seenB |= nb
            seenA |= na
            fA, fB = na, nb
        total += 2 * N - int(seenA.sum()) - int(seenB.sum())
    return total


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    """Annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, np.array(S, dtype=np.int64), D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, np.array(S2, dtype=np.int64), D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _attempt(N, d, D, rng, deadline):
    """Try random groups of order N until a valid connection set is found."""
    for _ in range(MAX_GROUPS):
        if time.monotonic() > deadline:
            return None
        desc = _random_group(N, rng)
        _, T, invs = _product_tables(desc)
        S = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 1:
        consider(2, [(0, 1)])
        return best

    # K_{d,d}: diameter 2, optimal for D = 2; valid fallback otherwise.
    consider(*lib.haar_graph(d, range(d)))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    # Projective plane incidence graph: optimal when d-1 is a prime power (D = 3).
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    if best[0] >= moore or d < 2:
        return best

    Nmax = min(moore // 2, MAX_N_TABLE)
    if Nmax < d:
        return best

    # Climb in order: search for lifts of order N just above the current best.
    lo = max(d, best[0] // 2 + 1)
    window = 6
    att_budget = 1.0
    fails = 0

    try:
        while time.monotonic() < deadline and lo <= Nmax:
            hi = min(Nmax, lo + window)
            N = rng.randint(lo, hi)
            att_deadline = min(deadline, time.monotonic() + att_budget)
            res = _attempt(N, d, D, rng, att_deadline)
            if res is not None:
                T, S = res
                edges = [(x, N + int(T[x, g])) for x in range(N) for g in S]
                consider(2 * N, edges)
                lo = max(N + 1, best[0] // 2 + 1)
                fails = 0
                continue
            fails += 1
            if fails % 3 == 0:
                window = min(window + 4, Nmax)
                att_budget = min(6.0, att_budget * 1.25)
    except Exception:
        pass  # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
