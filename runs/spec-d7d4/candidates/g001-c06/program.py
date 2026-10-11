"""Bi-Cayley Haar graphs over small non-cyclic groups, with walk-layer coverage certificates.

New idea: a Haar-type bipartite graph H(G, S) on two copies of a finite group G,
with a_x ~ b_{x s} for s in S, is vertex-transitive on each side under left
multiplication. Its diameter is at most D exactly when four walk-layer sets cover G:
the a-side and b-side reached from a_e in at most D steps, and the b-side reached
from b_e. These sets are computed with numpy from a group multiplication table, so no
BFS over the full graph is needed. The search hill-climbs over connection sets S
(with the identity fixed in S) for groups of orders just above the cyclic record size,
including semidirect products Z_m x| Z_k. Every returned graph is checked with lib.is_valid.
"""
import math
import random
import time

import numpy as np

import lib


def _group(m, k, r):
    """Multiplication and right-inverse tables of Z_m x|_r Z_k, element (a, b) coded as a*k+b."""
    N = m * k
    xs = np.arange(N, dtype=np.int64)
    a = xs // k
    b = xs % k
    powr = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    M = ((a[:, None] + powr[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    iv = np.argmax(M == 0, axis=1).astype(np.int64)
    return M, iv


def _reach(M, S, Sinv, N, D, start_a):
    """Coverage counts (a-side, b-side) reached by walks of length 1..D from a_e (start_a) or b_e."""
    cov_a = np.zeros(N, dtype=bool)
    cov_b = np.zeros(N, dtype=bool)
    front = np.zeros(1, dtype=np.int64)  # identity index
    on_a = start_a
    (cov_a if on_a else cov_b)[0] = True
    for _ in range(D):
        if on_a:
            front = np.unique(M[np.ix_(front, S)])
            cov_b[front] = True
        else:
            front = np.unique(M[np.ix_(front, Sinv)])
            cov_a[front] = True
        on_a = not on_a
    return int(cov_a.sum()), int(cov_b.sum())


def _cost(M, iv, S, Sinv, N, D):
    """Number of uncovered (start, vertex) pairs; zero iff the Haar graph has diameter <= D."""
    total = 0
    for start_a in (True, False):
        ca, cb = _reach(M, S, Sinv, N, D, start_a)
        total += 2 * N - ca - cb
    return total


def _climb(M, iv, N, d, D, rng, steps):
    """Hill-climb a connection set of size d containing the identity; return it or None."""
    S = np.array([0] + rng.sample(range(1, N), d - 1), dtype=np.int64)
    Sinv = iv[S]
    c = _cost(M, iv, S, Sinv, N, D)
    for _ in range(steps):
        if c == 0:
            break
        i = rng.randrange(1, d)
        cand = rng.randrange(1, N)
        if (S == cand).any():
            continue
        S2 = S.copy()
        S2[i] = cand
        S2inv = iv[S2]
        c2 = _cost(M, iv, S2, S2inv, N, D)
        if c2 <= c or rng.random() < 0.03:
            S, Sinv, c = S2, S2inv, c2
    return S if c == 0 else None


def _candidates(N, rng, cap):
    """Groups of order N: the cyclic group plus a couple of semidirect products Z_m x|_r Z_k."""
    out = [(N, 1, 1)]
    for k in range(2, N // 2 + 1):
        if N % k:
            continue
        m = N // k
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if rs:
            for r in rng.sample(rs, min(len(rs), 2)):
                out.append((m, k, r))
    rng.shuffle(out)
    return out[:cap]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    K = (2 * d, [(i, d + j) for i in range(d) for j in range(d)])
    if D == 2 or d == 1:
        return K

    if D == 3:
        special = []
        if lib.is_prime_power(d - 1):
            special.append(lib.projective_plane_incidence(d - 1))
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                special.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        for n, e in sorted(special, key=lambda g: -g[0]):
            if lib.is_valid(n, e, d, D):
                return n, e
        return K

    fallback = K
    Nmax = lib._moore_bound(d, D) // 2
    if Nmax <= d:
        return fallback
    rng = random.Random(seed)
    results = []  # (N, m, k, r, S)

    def try_group(N, m, k, r, steps):
        M, iv = _group(m, k, r)
        return _climb(M, iv, N, d, D, rng, steps)

    # Phase A: quick ascending sweep to collect easy successes.
    phase_a_end = start + 0.25 * (deadline - start)
    for N in range(d, Nmax + 1):
        if time.monotonic() > phase_a_end:
            break
        for (m, k, r) in _candidates(N, rng, 2):
            S = try_group(N, m, k, r, 80)
            if S is not None:
                results.append((N, m, k, r, S))
                break

    # Phase B: descending search above the best order, with growing step budgets.
    rnd = 0
    while time.monotonic() < deadline:
        best_now = max([x[0] for x in results], default=d)
        if best_now >= Nmax:
            break
        budget = min(300 * 3 ** rnd, 200000)
        hit = False
        for N in range(Nmax, best_now, -1):
            if time.monotonic() >= deadline:
                break
            for (m, k, r) in _candidates(N, rng, 3):
                if time.monotonic() >= deadline:
                    break
                S = try_group(N, m, k, r, budget)
                if S is not None:
                    results.append((N, m, k, r, S))
                    hit = True
                    break
            if hit:
                break
        rnd += 1

    # Certify the largest candidates with the library checker, falling back if needed.
    results.sort(key=lambda x: -x[0])
    for (N, m, k, r, S) in results[:5]:
        M, _ = _group(m, k, r)
        n = 2 * N
        edges = [(x, N + int(M[x, s])) for x in range(N) for s in S.tolist()]
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return fallback
