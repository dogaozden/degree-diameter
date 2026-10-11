import math
import random
import time

import numpy as np

import lib


def _group_table(m, k, r):
    """Right-multiplication table M[x, g] = x*g for Z_m x|_r Z_k (element (a, b) coded as a*k+b, identity 0),
    and invs[g] = inverse of g."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a, b = x // k, x % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    prod_a = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    prod_b = (b[:, None] + b[None, :]) % k
    M = prod_a * k + prod_b
    invs = np.argmax(M == 0, axis=0).astype(np.int64)
    return M, invs


def _groups_of_order(N):
    """All (m, k, r) with m*k = N giving the group Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m == 1:
            out.append((1, k, 0))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _unreached(M, S, Sinv, N, D, side):
    """Number of vertices not within distance D of the identity on the given side (bipartite BFS)."""
    seen = [np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)]
    seen[side][0] = True
    front = np.array([0], dtype=np.int64)
    cur = side
    for _ in range(D):
        if front.size == 0:
            break
        table = S if cur == 0 else Sinv
        nxt = 1 - cur
        mask = np.zeros(N, dtype=bool)
        mask[M[np.ix_(front, table)].ravel()] = True
        mask &= ~seen[nxt]
        seen[nxt] |= mask
        front = np.flatnonzero(mask)
        cur = nxt
    return 2 * N - int(seen[0].sum()) - int(seen[1].sum())


def _cost(M, invs, S, N, D):
    """Zero iff the bi-Cayley graph with connection set S has diameter <= D.
    Group acts regularly on each side, so checking from identity on both sides suffices."""
    S = np.asarray(S, dtype=np.int64)
    Sinv = invs[S]
    return _unreached(M, S, Sinv, N, D, 0) + _unreached(M, S, Sinv, N, D, 1)


def _anneal(M, invs, N, d, D, rng, t_end):
    """Simulated annealing over d-element subsets S of the group, minimizing unreached pairs."""
    S = rng.sample(range(N), d)
    cost = _cost(M, invs, S, N, D)
    t0 = time.monotonic()
    span = max(t_end - t0, 1e-3)
    while cost > 0:
        now = time.monotonic()
        if now >= t_end:
            return None
        T = 1.5 * (1.0 - (now - t0) / span) + 0.05
        i = rng.randrange(d)
        g = rng.randrange(N)
        if g in S:
            continue
        S2 = list(S)
        S2[i] = g
        c2 = _cost(M, invs, S2, N, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            S, cost = S2, c2
    return S


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    rng = random.Random(seed)
    N = max(d, 2)
    misses = 0
    SLICE = 1.2

    while time.monotonic() < deadline and misses < 3:
        groups = _groups_of_order(N)
        rng.shuffle(groups)
        found = None
        for m, k, r in groups[:4]:
            if time.monotonic() >= deadline:
                break
            if N <= d:
                break
            M, invs = _group_table(m, k, r)
            slice_end = min(deadline, time.monotonic() + SLICE)
            S = _anneal(M, invs, N, d, D, rng, slice_end)
            if S is None:
                continue
            edges = [(x, N + int(M[x, s])) for s in S for x in range(N)]
            n = 2 * N
            if lib.is_valid(n, edges, d, D):
                found = (n, edges)
                break
        if found:
            best = found
            misses = 0
        else:
            misses += 1
        N += 1

    return best
