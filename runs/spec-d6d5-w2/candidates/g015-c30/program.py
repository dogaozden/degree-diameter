import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Projective-plane baseline (D = 3, 4) and K_{d,d} fallback.
# ----------------------------------------------------------------------------

def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over semidirect products Z_m x| Z_k (non-abelian for r != 1).
#
# Vertices A_x = x and B_y = G + y, with x in G = Z_m x| Z_k (coded a*k+b).
# A connection set S of d distinct group elements gives edges A_x ~ B_{x*s}.
# Left multiplication by g is an automorphism, so the diameter is at most D
# iff every vertex is within D steps of A_1 and of B_1. That reach count is
# the cost; cost 0 gives a valid graph.
# ----------------------------------------------------------------------------

def _build_group(m, k, r):
    """Multiplication table M and inverse indices for Z_m x| Z_k with action r."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    # (a1,b1)*(a2,b2) = (a1 + r^b1 * a2, b1 + b2)
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    inv = np.argmax(M == 0, axis=1)
    return M, inv


def _candidate_groups(lo, hi, rng, cap):
    """(order, m, k, r) for semidirect groups with order in [lo, hi]; non-abelian first."""
    out = []
    for order in range(lo, hi + 1):
        for k in range(1, order + 1):
            if order % k:
                continue
            m = order // k
            if m < 2:
                continue
            if k == 1:
                out.append((order, m, 1, 1))
                continue
            rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            rng.shuffle(rs)
            for r in rs[:2]:
                out.append((order, m, k, r))
    nonab = [t for t in out if t[2] > 1]
    ab = [t for t in out if t[2] == 1]
    rng.shuffle(nonab)
    return (nonab + ab)[:cap]


def _adj(M, inv, S, G):
    """Adjacency array (2G, d): A-row x lists B-nodes G + x*s; B-row y lists A-nodes y*s^-1."""
    Sa = np.asarray(S, dtype=np.int64)
    return np.vstack([G + M[:, Sa], M[:, inv[Sa]]])


def _cost(adj, G, D):
    """Vertices not reached within D steps from A_1 (node 0) and B_1 (node G). Zero means valid."""
    N = adj.shape[0]
    total = 0
    for src in (0, G):
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = adj[frontier].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            frontier = nb
        total += N - int(np.count_nonzero(seen))
    return total


def _anneal_set(M, inv, G, d, D, deadline, rng):
    """Random restarts plus annealed swap moves on S (|S| = d). Returns S with cost 0, or None."""
    def cost(S):
        return _cost(_adj(M, inv, S, G), G, D)

    while time.monotonic() < deadline:
        S = rng.sample(range(G), d)
        c = cost(S)
        T = 1.0
        steps = 0
        while c > 0 and time.monotonic() < deadline and steps < 3000:
            steps += 1
            i = rng.randrange(d)
            x = rng.randrange(G)
            if x in S:
                continue
            S2 = list(S)
            S2[i] = x
            c2 = cost(S2)
            if c2 <= c or rng.random() < math.exp((c - c2) / T):
                S, c = S2, c2
            T = max(0.05, T * 0.999)
        if c == 0:
            return S
    return None


def _search_range(d, D, lo, hi, deadline, rng, on_found, floor):
    """Search groups with order in [lo, hi] with growing per-group budgets.

    floor[0] holds the best order found so far; only strictly larger orders are tried.
    """
    cands = _candidate_groups(lo, hi, rng, 60)
    cache = {}
    budget = 0.8
    while time.monotonic() < deadline and cands:
        tried = 0
        for (G, m, k, r) in cands:
            now = time.monotonic()
            if now >= deadline:
                return
            if G <= floor[0]:
                continue
            tried += 1
            key = (m, k, r)
            if key not in cache:
                cache[key] = _build_group(m, k, r)
            M, inv = cache[key]
            S = _anneal_set(M, inv, G, d, D, min(deadline, now + budget), rng)
            if S is not None:
                floor[0] = G
                on_found(G, M, S)
        if tried == 0:
            return
        budget *= 1.5


def _bc_edges(M, S, G):
    E = [(x, G + int(M[x, s])) for x in range(G) for s in S]
    return 2 * G, E


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    state = {"n": fb_n, "e": fb_e}

    def consider(n, e):
        if n > state["n"] and lib.is_valid(n, e, d, D):
            state["n"], state["e"] = n, e

    def consider_bi(G, M, S):
        n, e = _bc_edges(M, S, G)
        consider(n, e)

    if D in (3, 4):
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 5 and d >= 3:
        if (d, D) == (6, 5):
            # Bold target: non-abelian bi-Cayley graphs of order 2G > 684 first,
            # then smaller orders as a safety net.
            phases = [(343, 400, 0.60), (300, 342, 0.85)]
        else:
            mh = lib.moore_bound(d, D) // 2
            lo = max(2 * d, int(0.4 * mh))
            phases = [(lo, int(1.3 * lo) + 2, 0.85)]

        for lo, hi, frac in phases:
            if state["n"] >= 2 * hi:
                continue
            floor = [lo - 1]
            _search_range(d, D, lo, hi, start + frac * time_limit, rng, consider_bi, floor)

    n, e = state["n"], state["e"]
    if not lib.is_valid(n, e, d, D):
        n, e = lib.haar_graph(d, range(d))
    return n, e
