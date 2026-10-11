import math
import random
import time

import numpy as np

import lib


def _cost(m, S, D):
    """Number of vertices not within distance D of a_0 in the Haar graph H(m, S).

    The Haar graph is vertex-transitive (translations, plus the swap a_i -> b_{-i}),
    so checking eccentricity of a_0 is enough. Walk-endpoint sets X_t are computed
    exactly; their union over t <= D is the set of vertices within distance D.
    """
    Sa = np.asarray(S, dtype=np.int64)
    covA = np.zeros(m, dtype=bool)
    covB = np.zeros(m, dtype=bool)
    covA[0] = True
    nz = np.array([0], dtype=np.int64)
    for t in range(1, D + 1):
        if t % 2:  # A-side set to B-side set: b_{x+s}
            tg = (nz[:, None] + Sa[None, :]) % m
            Y = np.zeros(m, dtype=bool)
            Y[tg.ravel()] = True
            covB |= Y
        else:      # B-side set to A-side set: a_{y-s}
            tg = (nz[:, None] - Sa[None, :]) % m
            Y = np.zeros(m, dtype=bool)
            Y[tg.ravel()] = True
            covA |= Y
        nz = np.flatnonzero(Y)
    return int(2 * m - covA.sum() - covB.sum())


def _anneal(m, d, D, rng, S, deadline, iters=20000):
    """Simulated annealing over connection sets S (0 fixed in S[0]) for a fixed m."""
    S = list(S)
    cost = _cost(m, S, D)
    for it in range(iters):
        if cost == 0:
            return S, 0
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        T = 0.1 + 0.9 * (1.0 - it / iters)
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _cost(m, S, D)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
            cost = c2
        else:
            S[i] = old
    if cost == 0:
        return list(S), 0
    return None, cost


def _warm(prev_S, prev_m, m, d, rng):
    """Map a valid connection set from modulus prev_m to modulus m, then pad to size d."""
    rest = set()
    for s in prev_S:
        v = int(round(s * m / prev_m)) % m
        if v != 0:
            rest.add(v)
    rest = list(rest)
    while len(rest) < d - 1:
        x = rng.randrange(1, m)
        if x not in rest:
            rest.append(x)
    return [0] + rest[:d - 1]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)

    if D <= 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    base = lib.haar_graph(d, range(d))  # K_{d,d}: diameter 2, always valid
    if d < 3 or D <= 2:
        return base

    rng = random.Random(seed)
    upper = lib._moore_bound(d, D) // 2  # Haar order 2m must not exceed the Moore bound

    history = [(d, list(range(d)))]
    m = d + 1
    prev_m, prev_S = d, list(range(d))

    while time.monotonic() < deadline and m <= upper:
        S0 = _warm(prev_S, prev_m, m, d, rng)
        S, _ = _anneal(m, d, D, rng, S0, deadline)
        if S is not None:
            history.append((m, S))
            prev_m, prev_S = m, S
            m += 1
        # on failure, retry the same m with fresh annealing randomness

    # Verify with the exact library checker; fall back to the largest valid success.
    for mm, SS in reversed(history):
        n, edges = lib.haar_graph(mm, SS)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return base
