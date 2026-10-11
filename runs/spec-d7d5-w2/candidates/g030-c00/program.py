import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline: K_{d,d} (diameter 2) and the exact projective-plane incidence
# graph when d - 1 is a prime power (diameter 3, Moore-optimal).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: Haar graphs over non-abelian groups.
#
# Group G = Z_m x| Z_k (semidirect, element a*k+b). Vertices a_g and b_h for
# g, h in G. Connection set S = {s_1..s_d} (distinct), edges a_g ~ b_{g s}.
# Every vertex has degree d and the graph is bipartite.
#
# Left multiplication by any h is an automorphism swapping nothing and
# acting transitively on each side, so the diameter equals the maximum
# eccentricity of a_1 and b_1 only. Each candidate is scored with two BFS
# runs in numpy, and a hill climb replaces one element of S at a time to
# minimise the number of pairs at distance > D from those two sources.
# Groups are sampled with order just above the current best, so the
# search climbs the order ladder.
# ----------------------------------------------------------------------------

def _semidirect_mul_table(m, k, r):
    """Return (M, inv) where M[g, h] = g*h and inv[g] is the inverse of g, for Z_m x| Z_k."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    powers = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    inv = np.empty(G, dtype=np.int64)
    rows, cols = np.nonzero(M == 0)  # identity is index 0
    inv[rows] = cols
    return M, inv


def _sample_group(T, rng):
    """Return (m, k, r) for Z_m x| Z_k with order m*k >= T (a few random choices), or None."""
    for _ in range(200):
        k = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16])
        m = -(-T // k) + rng.randrange(0, 4)
        if m < 2:
            continue
        r = 1
        if k > 1:
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
                    r = c
                    break
        return m, k, r
    return None


def _cost(nbr, G, D):
    """Number of (source, vertex) pairs at distance > D, for sources a_1 (index 0) and b_1 (index G)."""
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nxt = nbr[frontier].ravel()
            nxt = np.unique(nxt[~seen[nxt]])
            if nxt.size == 0:
                break
            seen[nxt] = True
            frontier = nxt
        total += N - int(seen.sum())
    return total


def _try_group(M, inv, G, d, D, rng, deadline, patience):
    """Hill climb over connection sets S in the group G. Returns S (list of d elements) or None."""
    N = 2 * G
    ga = np.arange(G, dtype=np.int64)
    nbr = np.empty((N, d), dtype=np.int64)

    def set_col(l, s):
        nbr[:G, l] = G + M[ga, s]
        nbr[G:, l] = M[ga, inv[s]]

    S = rng.sample(range(G), d)
    for l, s in enumerate(S):
        set_col(l, s)
    cost = _cost(nbr, G, D)
    stall = 0
    while cost > 0 and stall < patience:
        if time.monotonic() > deadline:
            break
        l = rng.randrange(d)
        old = S[l]
        new = rng.randrange(G)
        if new in S:
            stall += 1
            continue
        S[l] = new
        set_col(l, new)
        c2 = _cost(nbr, G, D)
        if c2 <= cost:
            stall = 0 if c2 < cost else stall + 1
            cost = c2
        else:
            S[l] = old
            set_col(l, old)
            stall += 1
    if cost == 0:
        return S
    return None


def _haar_edges(M, G, S):
    """Edges of the bi-Cayley graph: a_g ~ b_{g s} for s in S."""
    edges = []
    for s in S:
        for g in range(G):
            edges.append((g, G + int(M[g, s])))
    return edges


# ----------------------------------------------------------------------------
# Greedy pair insertion (grow the order by 2 while staying valid).
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    """Return a proper 2-colouring (list of 0/1), or None if not bipartite."""
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _extend(n, edges, d, D, rng, deadline, max_fail=200):
    """Repeatedly add two vertices x (side A), y (side B) by rewiring d-1 edges."""
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    fails = 0
    while time.monotonic() < deadline and fails < max_fail:
        order = list(range(len(edges)))
        rng.shuffle(order)
        chosen = []
        used_a, used_b = set(), set()
        for t in order:
            if len(chosen) == d - 1:
                break
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            if a in used_a or b in used_b:
                continue
            chosen.append(t)
            used_a.add(a)
            used_b.add(b)
        if len(chosen) < d - 1:
            break
        x, y = n, n + 1
        cs = set(chosen)
        cand = [e for t, e in enumerate(edges) if t not in cs]
        for t in chosen:
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            cand.append((x, b))
            cand.append((y, a))
        cand.append((x, y))
        if lib.is_valid(n + 2, cand, d, D):
            edges = cand
            n += 2
            color.extend([0, 1])
            fails = 0
        else:
            fails += 1
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    search_deadline = start + 0.8 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D <= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D <= 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    # Exact construction for D = 3 when d - 1 is a prime power.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best

    # New construction: hill-climbed Haar graphs over semidirect products.
    # Target group order starts just above the current best (order = n/2).
    T = best_n // 2 + 1
    while time.monotonic() < search_deadline:
        g = _sample_group(max(T, d), rng)
        if g is None:
            continue
        m, k, r = g
        G = m * k
        if G < d or 2 * G <= best_n:
            T = max(T, best_n // 2 + 1)
            continue
        M, inv = _semidirect_mul_table(m, k, r)
        S = _try_group(M, inv, G, d, D, rng, search_deadline, patience=800)
        if S is not None:
            edges = _haar_edges(M, G, S)
            if consider(2 * G, edges):
                # Climb: aim for larger groups next.
                T = G + 1
                continue
        T = best_n // 2 + 1 + rng.randrange(0, 4)

    # Greedy pair insertion on the best graph found so far.
    try:
        n2, e2 = _extend(best_n, best[1], d, D, rng, deadline)
        if n2 > best_n:
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
