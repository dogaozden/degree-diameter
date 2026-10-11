import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: Haar graphs (bi-Cayley graphs with one vertex per side)
# over finite groups G = Z_m x|_r Z_k, of order N.
#
# Vertices a_x (x in G) and b_y (y in G); a_x ~ b_{x s} for s in S, |S| = d.
# Left multiplication is an automorphism that preserves both sides, so the
# diameter is controlled by two BFS runs, from a_e and from b_e. S is normalised
# to contain the identity (right translation of S gives an isomorphic graph),
# and the search is simulated annealing over the other d-1 elements of S.
# The order is 2N, so the goal is a group of order N >= record/2 + 1.
# ----------------------------------------------------------------------------

def _tables(m, k, r):
    """Multiplication table M and inverse array for Z_m x|_r Z_k, coded a*k+b; identity is 0."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    inv = np.argmax(M == 0, axis=1).astype(np.int64)
    return N, M, inv


def _groups(N, rng):
    """Candidate (m, k, r) with m*k = N: cyclic/abelian and a few semidirect choices."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [1]
        if k > 1 and m > 2:
            for _ in range(60):
                r = rng.randrange(2, m)
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m and r not in rs:
                    rs.append(r)
                if len(rs) >= 3:
                    break
        for r in rs:
            out.append((m, k, r))
    rng.shuffle(out)
    return out


def _cost(adj, N, D):
    """Unreached vertices within distance D from a_e and from b_e (0 means valid)."""
    total = 0
    for src in (0, N):
        vis = np.zeros(2 * N, dtype=bool)
        vis[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = adj[front].ravel()
            nb = nb[~vis[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            vis[nb] = True
            front = nb
        total += 2 * N - int(vis.sum())
    return total


def _make_adj(S, M, inv, N):
    """Adjacency of the Haar graph: a_x -> b_{x s}, b_y -> a_{y s^-1}."""
    invS = inv[S]
    adj = np.empty((2 * N, len(S)), dtype=np.int64)
    adj[:N] = N + M[:, S]
    adj[N:] = M[:, invS]
    return adj


def _anneal(d, D, N, M, inv, rng, iters, deadline):
    """Search a connection set S (identity included, |S| = d) with diameter <= D. Returns S or None."""
    if N < d:
        return None
    S = np.array([0] + rng.sample(range(1, N), d - 1), dtype=np.int64)
    adj = _make_adj(S, M, inv, N)
    cost = _cost(adj, N, D)
    for t in range(iters):
        if cost == 0:
            break
        if time.monotonic() > deadline:
            return None
        T = max(0.05, 1.5 * (1.0 - t / iters))
        i = rng.randrange(1, d)
        new = rng.randrange(1, N)
        if np.any(S == new):
            continue
        old = int(S[i])
        S[i] = new
        adj2 = _make_adj(S, M, inv, N)
        c2 = _cost(adj2, N, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            adj = adj2
        else:
            S[i] = old
    if cost != 0:
        return None
    return S


def _haar_edges(N, M, S):
    """Edges of the Haar graph on 2N vertices: A = 0..N-1, B = N..2N-1."""
    return [(x, N + int(M[x, s])) for x in range(N) for s in S]


def _try_order(d, D, N, rng, deadline, iters, max_groups):
    """Try several groups of order N; return a valid edge list for 2N vertices, or None."""
    for (m, k, r) in _groups(N, rng)[:max_groups]:
        if time.monotonic() > deadline:
            return None
        Nn, M, inv = _tables(m, k, r)
        S = _anneal(d, D, Nn, M, inv, rng, iters, deadline)
        if S is not None:
            return 2 * Nn, _haar_edges(Nn, M, S)
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    moore = lib._moore_bound(d, D)
    lo = best_n // 2
    inc = 1
    while time.monotonic() < deadline:
        N = lo + inc
        if inc == 1:
            N += rng.randrange(0, 3)
        if 2 * N > moore:
            inc = max(1, inc // 2)
            if lo + 1 > moore // 2:
                break
            continue
        res = _try_order(d, D, N, rng, deadline, 2500, 4)
        if res is not None:
            consider(res[0], res[1])
            lo = N
            inc = min(inc * 2, 64)
        else:
            inc = max(1, inc // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
