import math
import random
import time

import numpy as np

import lib

# ----------------------------------------------------------------------------
# Bold change: instead of hill-climbing or greedy covers, search bi-Cayley
# graphs over semidirect products Z_m x|_r Z_k with a vectorised numpy
# reachability cost and simulated annealing. The order N is swept upward
# from the smallest value that would beat the current best, so every
# success raises the bar for the next order.
#
# Bi-Cayley graph: A_x ~ B_{x*s} for s in S, with A_x = x and B_y = N + y.
# Left translation is an automorphism of each side, so checking the
# eccentricity of A_0 and B_0 suffices for diameter D.
# ----------------------------------------------------------------------------

MAX_GROUPS = 5       # groups tried per order N before moving to N + 1
ANNEAL_ITERS = 4000  # annealing steps per group


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
    """Return (colT, invT): colT[s][x] = x*s and invT[s] = s^-1, vectorised."""
    N = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    # mul[x, g] = (a_x + r^{b_x} a_g mod m, b_x + b_g mod k), coded a*k + b.
    mul = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    colT = np.ascontiguousarray(mul.T)
    invT = np.argmax(mul == 0, axis=1).tolist()  # g * h = identity (code 0)
    return colT, invT


def _anneal(N, d, D, colT, invT, rng, deadline, iters):
    """Anneal a connection set S (0 always included, WLOG) to zero unreached pairs."""
    if N < d or d < 2:
        return None

    def unreached(S):
        cols = [colT[s] for s in S]
        icols = [colT[invT[s]] for s in S]
        total = 0
        for src in (0, N):
            reach = np.zeros(2 * N, dtype=bool)
            reach[src] = True
            count = 1
            for _ in range(D):
                ia = np.nonzero(reach[:N])[0]
                ib = np.nonzero(reach[N:])[0]
                new = np.zeros(2 * N, dtype=bool)
                for c, ic in zip(cols, icols):
                    new[N + c[ia]] = True   # A_x -> B_{x s}
                    new[ic[ib]] = True      # B_y -> A_{y s^-1}
                reach |= new
                nc = int(np.count_nonzero(reach))
                if nc == count:
                    break
                count = nc
            total += 2 * N - count
        return total

    S = [0] + rng.sample(range(1, N), d - 1)
    cost = unreached(S)
    if cost == 0:
        return S
    T0 = max(1.0, 0.05 * cost)
    T_end = 0.3
    decay = (T_end / T0) ** (1.0 / max(1, iters))
    T = T0
    for it in range(iters):
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = unreached(S)
        if v <= cost or rng.random() < math.exp(-(v - cost) / T):
            cost = v
            if cost == 0:
                return list(S)
        else:
            S[i] = old
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 5.0))
    deadline = t0 + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2 <= D.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    # Structured baseline for D = 3: projective plane of largest order q <= d-1.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                break

    if best[0] >= moore:
        return best

    rng = random.Random(seed * 1000003 + d * 131 + D)
    N = max(best[0] // 2 + 1, d)

    while time.monotonic() < deadline and 2 * N <= moore:
        found = None
        found_tab = None
        groups = _groups(N)
        rng.shuffle(groups)
        for m, k, r in groups[:MAX_GROUPS]:
            if time.monotonic() >= deadline:
                break
            colT, invT = _tables(m, k, r)
            S = _anneal(N, d, D, colT, invT, rng, deadline, ANNEAL_ITERS)
            if S is not None:
                found = S
                found_tab = colT
                break
        if found is not None:
            edges = [(x, N + int(found_tab[s][x])) for x in range(N) for s in found]
            consider(2 * N, edges)
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
