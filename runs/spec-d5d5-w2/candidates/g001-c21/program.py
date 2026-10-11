import math
import random
import time

import numpy as np

import lib


def _fallback(d, D):
    """A small graph that is valid by construction, checked with lib.is_valid."""
    cands = []
    if d >= 1 and D >= 2:
        cands.append(lib.haar_graph(d, range(d)))   # K_{d,d}, diameter 2
    cands.append((2, [(0, 1)]))
    for n, e in cands:
        if lib.is_valid(n, e, d, D):
            return n, e
    return 1, []


def _semidirect_table(m, k, r):
    """Multiplication and inversion tables of Z_m x|_r Z_k, element (a, b) coded as a*k+b."""
    x = np.arange(m * k, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)  # r^b mod m
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    B = (b[:, None] + b[None, :]) % k
    mt = A * k + B
    nb = (-b) % k
    ia = (-(pw[nb] * a)) % m
    inv = ia * k + nb
    return mt, inv


def _group_descriptors(N, rng, cap):
    """(m, k, r) for every semidirect product of order N = m*k (r = 1 when k = 1, cyclic)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if k == 1:
            out.append((m, 1, 1))
            continue
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    rng.shuffle(out)
    return out[:cap]


def _covers(mt, inv, S, N, D):
    """Bi-Cayley graph with A-vertex x ~ B-vertex x*s is diameter <= D iff BFS from A-vertex 0 reaches all.

    Left translation acts transitively on each side, so one BFS suffices.
    """
    invS = inv[S]
    visited = np.zeros(2 * N, dtype=bool)
    visited[0] = True
    front = np.array([0], dtype=np.int64)
    for _ in range(D):
        parts = []
        fa = front[front < N]
        fb = front[front >= N] - N
        if fa.size:
            parts.append(N + mt[fa][:, S].ravel())
        if fb.size:
            parts.append(mt[fb][:, invS].ravel())
        if not parts:
            break
        cand = np.unique(np.concatenate(parts))
        cand = cand[~visited[cand]]
        if cand.size == 0:
            break
        visited[cand] = True
        front = cand
    return bool(visited.all())


def _edges(mt, S, N):
    edges = []
    for s in S.tolist():
        col = (N + mt[:, s]).tolist()
        edges.extend((x, col[x]) for x in range(N))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    rng = random.Random(seed)
    best = _fallback(d, D)
    best_N = best[0] // 2
    Nmax = lib.moore_bound(d, D) // 2

    # Search bi-Cayley graphs over non-abelian groups of increasing order N.
    # Each order N gets all remaining time until a valid graph is found.
    N = max(best_N + 1, d + 1)
    while N <= Nmax and time.monotonic() < deadline:
        groups = [_semidirect_table(m, k, r)
                  for (m, k, r) in _group_descriptors(N, rng, 24)]
        found = None
        while time.monotonic() < deadline:
            mt, inv = groups[rng.randrange(len(groups))]
            S = np.array(rng.sample(range(N), d), dtype=np.int64)
            if _covers(mt, inv, S, N, D):
                edges = _edges(mt, S, N)
                n = 2 * N
                if lib.is_valid(n, edges, d, D):
                    found = (n, edges)
                    break
        if found is None:
            break
        best = found
        best_N = N
        N += 1

    return best
