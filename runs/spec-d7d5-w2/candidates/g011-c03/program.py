import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over small groups Z_m x| Z_k2 (single base pair per side).
#
# Vertices: A_g = g (0 <= g < G), B_h = G + h.
# Connection set S of size d (distinct elements): A_g ~ B_{g*s} for s in S.
# Left multiplication is an automorphism, so the graph is transitive on each side.
# Hence diameter <= D iff A_e and B_e both reach every vertex within D steps.
#
# Search: for a target order 2G, sample a group, then hill-climb on S, minimizing
# the number of vertices unreached from A_e and B_e within D steps.
# The order grows adaptively; every returned graph passes lib.is_valid.
# ----------------------------------------------------------------------------


def _divisors(n):
    return [k for k in range(1, n + 1) if n % k == 0]


def _tables(m, k2, r):
    """Return (Ts, Invs) with Ts[s, g] = g*s and Invs[s, h] = g such that g*s = h."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return Ts, Invs


def _cost(nb, G, D):
    """Number of (source, vertex) pairs not within distance D, for sources A_e and B_e."""
    N = 2 * G
    bad = 0
    for src in (0, G):
        vis = np.zeros(N, dtype=bool)
        vis[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            nxt = nb[front].ravel()
            nxt = nxt[~vis[nxt]]
            if nxt.size == 0:
                break
            nxt = np.unique(nxt)
            vis[nxt] = True
            front = nxt
        bad += N - int(vis.sum())
    return bad


def _attempt(G, d, D, rng, deadline, iters):
    """Try to find a valid bi-Cayley graph of order 2G. Returns (S, Ts) or None."""
    if G < d:
        return None
    k2 = rng.choice(_divisors(G))
    m = G // k2
    r = 1 % m
    if k2 > 1 and m > 2 and rng.random() < 0.8:
        for _ in range(60):
            c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
    Ts, Invs = _tables(m, k2, r)

    S = rng.sample(range(G), d)
    N = 2 * G
    nb = np.empty((N, d), dtype=np.int64)
    for j, s in enumerate(S):
        nb[:G, j] = G + Ts[s]
        nb[G:, j] = Invs[s]

    cur = _cost(nb, G, D)
    for _ in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        j = rng.randrange(d)
        s_new = rng.randrange(G)
        if s_new in S:
            continue
        s_old = S[j]
        old_col = nb[:, j].copy()
        S[j] = s_new
        nb[:G, j] = G + Ts[s_new]
        nb[G:, j] = Invs[s_new]
        c = _cost(nb, G, D)
        if c <= cur or rng.random() < 0.01:
            cur = c
        else:
            S[j] = s_old
            nb[:, j] = old_col
    if cur == 0:
        return S, Ts
    return None


def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_edges = lib.haar_graph(d, range(d))
    best = (best_n, best_edges)

    try:
        pg = _pg_fallback(d) if D >= 3 else None
        if pg is not None and lib.is_valid(pg[0], pg[1], d, D):
            if pg[0] > best[0]:
                best = pg
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    except Exception:
        pass

    try:
        rng = random.Random(seed)
        G_ok = best[0] // 2
        step = max(1, G_ok // 20)
        while time.monotonic() < deadline:
            G = G_ok + step
            res = None
            for _ in range(3):
                if time.monotonic() >= deadline:
                    break
                res = _attempt(G, d, D, rng, deadline, 1500)
                if res is not None:
                    break
            if res is None:
                step = max(1, step // 2)
                continue
            S, Ts = res
            row = Ts[S]  # d x G
            edges = [(g, G + int(row[j, g])) for g in range(G) for j in range(d)]
            if lib.is_valid(2 * G, edges, d, D):
                best = (2 * G, edges)
                G_ok = G
                step = step * 2
            else:
                step = max(1, step // 2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
