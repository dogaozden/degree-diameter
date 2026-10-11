import math
import random
import time

import numpy as np

import lib

ITERS = 1200       # annealing steps per restart
RESTARTS = 2       # fresh random lift per attempt
MAX_P = 4          # base vertices per side in the voltage lift


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


def _tables(m, k, r):
    """Vectorised multiplication table Tm[x, g] and inverse array for Z_m x|_r Z_k.

    Element (a, b) is coded a*k + b; identity is 0.
    """
    N = m * k
    r %= m
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    nk = (-b) % k
    invs = ((-pw[nk] * a) % m) * k + nk
    newa = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    newb = (b[:, None] + b[None, :]) % k
    Tm = newa * k + newb
    return Tm, invs


def _unreached(p, N, d, D, sig, V, Tm, invs):
    """Count (source, vertex) pairs at distance > D for one source per base fibre.

    Base graph: A_i -- B_{sig[k][i]} with voltage V[i][k] for each k < d.
    Lift: A_{i,x} ~ B_{j, x*g}. Left multiplication is an automorphism, so one
    source per fibre suffices.
    """
    S = 2 * p
    darts = []
    for k in range(d):
        for i in range(p):
            j = sig[k][i]
            g = V[i][k]
            darts.append((i, j, Tm[:, invs[g]], Tm[:, g]))
    RA = np.zeros((S, p, N), dtype=bool)
    RB = np.zeros((S, p, N), dtype=bool)
    for s in range(p):
        RA[s, s, 0] = True
        RB[p + s, s, 0] = True
    for _ in range(D):
        nA = RA.copy()
        nB = RB.copy()
        for i, j, gA, gB in darts:
            nB[:, j, :] |= RA[:, i, :][:, gA]
            nA[:, i, :] |= RB[:, j, :][:, gB]
        RA, RB = nA, nB
    reached = int(RA.sum()) + int(RB.sum())
    return S * 2 * p * N - reached


def _anneal(p, N, d, D, rng, Tm, invs, iters, deadline):
    """Simulated annealing over base permutations and voltages to zero unreached pairs."""
    sig = [rng.sample(range(p), p) for _ in range(d)]
    V = [[rng.randrange(N) for _ in range(d)] for _ in range(p)]
    cur = _unreached(p, N, d, D, sig, V, Tm, invs)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = max(0.2, 3.0 * (1.0 - it / iters))
        if p > 1 and rng.random() < 0.2:
            k = rng.randrange(d)
            a, b = rng.sample(range(p), 2)
            sig2 = [row[:] for row in sig]
            sig2[k][a], sig2[k][b] = sig2[k][b], sig2[k][a]
            V2 = V
        else:
            sig2 = sig
            i = rng.randrange(p)
            k = rng.randrange(d)
            V2 = [row[:] for row in V]
            V2[i][k] = rng.randrange(N)
        v = _unreached(p, N, d, D, sig2, V2, Tm, invs)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            sig, V, cur = sig2, V2, v
    return (sig, V) if cur == 0 else None


def _attempt(p, N, d, D, rng, Tm, invs, deadline):
    for _ in range(RESTARTS):
        if time.monotonic() >= deadline:
            return None
        res = _anneal(p, N, d, D, rng, Tm, invs, ITERS, deadline)
        if res is not None:
            return res
    return None


def _edges(p, N, d, sig, V, Tm):
    """Explicit edge list of the lift; A-vertices are 0..pN-1, B-vertices pN..2pN-1."""
    E = set()
    for k in range(d):
        for i in range(p):
            j = sig[k][i]
            g = V[i][k]
            for x in range(N):
                a = i * N + x
                b = p * N + j * N + int(Tm[x, g])
                E.add((a, b))
    return list(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 6.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

    # Safe baselines.
    consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best[0], best[1]

    M = lib._moore_bound(d, D)
    budget = 2.0
    fails = 0

    while time.monotonic() < deadline:
        opts = []
        for p in range(1, MAX_P + 1):
            lo = best[0] // (2 * p) + 1
            hi = M // (2 * p)
            if lo <= hi:
                opts.append((p, lo, hi))
        if not opts:
            break
        p, lo, hi = rng.choice(opts)
        N = rng.randint(lo, min(hi, lo + 6))
        groups = _groups(N)
        if not groups:
            continue
        m, k, r = rng.choice(groups)
        Tm, invs = _tables(m, k, r)
        att_dl = min(deadline, time.monotonic() + budget)
        res = _attempt(p, N, d, D, rng, Tm, invs, att_dl)
        if res is None:
            fails += 1
            if fails % 8 == 0:
                budget = min(budget * 1.3, 15.0)
            continue
        sig, V = res
        consider(2 * p * N, _edges(p, N, d, sig, V, Tm))

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
