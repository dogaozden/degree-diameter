import math
import random
import time

import numpy as np

import lib

_PENALTY = 10 ** 6  # cost added per duplicate dart


def _groups(G):
    """Semidirect parameters (m, k, r) with m*k = G, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(m, k, r):
    """Vectorised multiplication table M[x, y] = x*y and inverse array for Z_m x|_r Z_k."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    M = M.astype(np.int64)
    invs = np.argmax(M == 0, axis=1).astype(np.int64)
    return G, M, invs


def _nbr(k, G, d, M, invs, V, P):
    """Neighbour array (2kG x d). A_{i,x} ~ B_{P[L][i], x*V[L][i]} in layer L."""
    N2 = 2 * k * G
    nbr = np.empty((N2, d), dtype=np.int64)
    ar = np.arange(G, dtype=np.int64)
    for L in range(d):
        for i in range(k):
            s = V[L][i]
            j = P[L][i]
            nbr[i * G:(i + 1) * G, L] = (k + j) * G + M[:, s]
            nbr[(k + j) * G:(k + j + 1) * G, L] = i * G + M[ar, invs[s]]
    return nbr


def _cost(k, G, d, D, M, invs, V, P):
    """Unreached (representative, vertex) pairs from one vertex per base orbit, plus duplicate penalties."""
    keys = set()
    dup = 0
    for L in range(d):
        for i in range(k):
            key = (i, P[L][i], V[L][i])
            if key in keys:
                dup += 1
            keys.add(key)
    nbr = _nbr(k, G, d, M, invs, V, P)
    N2 = 2 * k * G
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = np.zeros(N2, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        cnt = 1
        for _ in range(D):
            nb = nbr[frontier].ravel()
            nb = np.unique(nb[~seen[nb]])
            if nb.size == 0:
                break
            seen[nb] = True
            cnt += int(nb.size)
            frontier = nb
        total += N2 - cnt
    return total + _PENALTY * dup


def _anneal(d, D, k, G, M, invs, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer base permutations."""
    V = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    P = [rng.sample(range(k), k) for _ in range(d)]
    cost = _cost(k, G, d, D, M, invs, V, P)
    T0, T1 = 4.0, 0.1
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        L = rng.randrange(d)
        if k == 1 or rng.random() < 0.75:
            i = rng.randrange(k)
            old = V[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            V[L][i] = new
            c2 = _cost(k, G, d, D, M, invs, V, P)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                V[L][i] = old
        else:
            a, b = rng.sample(range(k), 2)
            P[L][a], P[L][b] = P[L][b], P[L][a]
            c2 = _cost(k, G, d, D, M, invs, V, P)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                P[L][a], P[L][b] = P[L][b], P[L][a]
    if cost == 0:
        return V, P
    return None


def _edges(k, G, d, M, V, P):
    """Edge list of the lift; returns (n, edges)."""
    E = []
    for L in range(d):
        for i in range(k):
            s = V[L][i]
            j = P[L][i]
            col = M[:, s].tolist()
            for g in range(G):
                E.append((i * G + g, (k + j) * G + col[g]))
    return 2 * k * G, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    if best[0] >= moore:
        return best

    ks = (1, 2, 3, 4)
    while time.monotonic() < deadline and best[0] < moore:
        feasible = [k for k in ks if 2 * k * (best[0] // (2 * k) + 1) <= moore]
        if not feasible:
            break
        k = rng.choice(feasible)
        lo = best[0] // (2 * k) + 1
        G = lo + rng.randrange(max(3, lo // 15))
        groups = _groups(G)
        if not groups:
            continue
        m, kk, r = rng.choice(groups)
        G, M, invs = _table(m, kk, r)
        sub_deadline = min(deadline, time.monotonic() + max(1.0, budget / 6.0))
        res = _anneal(d, D, k, G, M, invs, rng, sub_deadline, 3000)
        if res is not None:
            V, P = res
            n, E = _edges(k, G, d, M, V, P)
            if n > best[0] and lib.is_valid(n, E, d, D):
                best = (n, E)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
