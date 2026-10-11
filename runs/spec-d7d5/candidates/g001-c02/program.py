import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over small finite groups, searched with numpy.
#
# Group G (order G), connection set S = {s_1..s_d} with distinct elements.
# Vertices A_g = g and B_h = G + h. Edge A_g -- B_{g*s} for every s in S.
# Left multiplication is an automorphism, so distances from A_e and B_e
# determine the diameter. Simulated annealing on S minimises the number of
# (source, vertex) pairs left beyond distance D.
#
# Groups are semidirect products Z_m x| Z_k (including cyclic and direct
# products), built as explicit multiplication tables.
# ----------------------------------------------------------------------------


def _divisors(n):
    return [k for k in range(1, n + 1) if n % k == 0]


def _build_group(m, k, r):
    """Multiplication table of Z_m x|_r Z_k as (Mt, Mtinv): Mt[s][g] = g*s, Mtinv[s][h] = h*s^-1."""
    order = m * k
    idx = np.arange(order, dtype=np.int64)
    a = idx // k
    b = idx % k
    pw = np.array([pow(r, bb, m) for bb in range(k)], dtype=np.int64)
    # (a1,b1)*(a2,b2) = (a1 + r^b1 * a2, b1 + b2)
    prod = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    Mt = np.ascontiguousarray(prod.T).astype(np.intp)
    inv = np.argmax(prod == 0, axis=1)  # identity is index 0
    Mtinv = np.ascontiguousarray(Mt[inv])
    return Mt, Mtinv


def _random_group(G, rng):
    """Random semidirect product of order G, returned as (Mt, Mtinv), or None."""
    cands = [k for k in _divisors(G) if G // k >= 2]
    if not cands:
        return None
    for _ in range(40):
        k = rng.choice(cands)
        m = G // k
        if k == 1 or rng.random() < 0.25:
            r = 1
        else:
            r = None
            for _t in range(60):
                x = rng.randrange(1, m)
                if math.gcd(x, m) == 1 and pow(x, k, m) == 1 % m:
                    r = x
                    break
            if r is None:
                continue
        return _build_group(m, k, r)
    return None


def _cost(Mt, Mtinv, S, G, D):
    """Number of (source, vertex) pairs at distance > D from sources A_e and B_e. Zero means valid."""
    total = 0
    for side in (0, 1):
        seenA = np.zeros(G, dtype=bool)
        seenB = np.zeros(G, dtype=bool)
        fA = np.zeros(G, dtype=bool)
        fB = np.zeros(G, dtype=bool)
        if side == 0:
            fA[0] = True
            seenA[0] = True
        else:
            fB[0] = True
            seenB[0] = True
        for _ in range(D):
            nb = np.zeros(G, dtype=bool)
            na = np.zeros(G, dtype=bool)
            for s in S:
                nb[Mt[s]] |= fA      # A -> B along g -> g*s
                na[Mtinv[s]] |= fB   # B -> A along h -> h*s^-1
            nb &= ~seenB
            na &= ~seenA
            seenB |= nb
            seenA |= na
            fA, fB = na, nb
            if not (fA.any() or fB.any()):
                break
        total += 2 * G - int(seenA.sum()) - int(seenB.sum())
    return total


def _anneal(Mt, Mtinv, G, d, D, rng, deadline, iters):
    """Anneal a d-element connection set; return it if the bi-Cayley graph has diameter <= D."""
    S = rng.sample(range(G), d)
    cost = _cost(Mt, Mtinv, S, G, D)
    if cost == 0:
        return S
    T0 = max(1.0, 0.01 * cost)
    T1 = 0.3
    for it in range(iters):
        if time.monotonic() >= deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        i = rng.randrange(d)
        cand = rng.randrange(G)
        if cand in S:
            continue
        old = S[i]
        S[i] = cand
        c2 = _cost(Mt, Mtinv, S, G, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost == 0:
                return S
        else:
            S[i] = old
    return None


def _kdd(d):
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = _kdd(d)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Projective plane incidence graph of the largest prime power q <= d - 1 (diameter 3).
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break

    # Main search: bi-Cayley graphs over random semidirect products, just above the current best.
    while time.monotonic() < deadline:
        lo = max(best_n // 2 + 1, d)
        if rng.random() < 0.7:
            G = lo + rng.randrange(0, 4)
        else:
            G = lo + rng.randrange(0, 40)
        if G > 1600:
            break
        grp = _random_group(G, rng)
        if grp is None:
            continue
        Mt, Mtinv = grp
        S = _anneal(Mt, Mtinv, G, d, D, rng, deadline, iters=3000)
        if S is not None:
            edges = [(g, G + h) for s in S for g, h in enumerate(Mt[s].tolist())]
            consider(2 * G, edges)

    if not lib.is_valid(best_n, best_e, d, D):
        return _kdd(d)
    return best_n, best_e
