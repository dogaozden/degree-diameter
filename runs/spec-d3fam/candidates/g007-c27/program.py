import math
import random
import time

import numpy as np

import lib


def _cost(M):
    """Number of ordered vertex pairs at distance > 3 in the bipartite graph with biadjacency M (square)."""
    F = M.astype(np.float32)
    G = F @ F.T          # A-A common neighbours (distance 2 when > 0)
    G2 = F.T @ F         # B-B common neighbours
    H = G @ F            # walks a -> b' -> a' -> b of length 3
    return (int(np.count_nonzero(G == 0))
            + int(np.count_nonzero(G2 == 0))
            + int(np.count_nonzero((F == 0) & (H == 0))))


def _two_colour(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
                elif col[v] == col[u]:
                    return None
    return col


def _to_graph(M):
    m = M.shape[0]
    rows, cols = np.nonzero(M)
    return 2 * m, [(int(a), m + int(b)) for a, b in zip(rows, cols)]


def _splice(M, E, d, rng):
    """Add one A vertex x and one B vertex y by removing a matching of d edges
    (a_i, b_i) and joining x to all b_i and y to all a_i. Keeps d-regularity."""
    m = M.shape[0]
    order = list(range(len(E)))
    rng.shuffle(order)
    usedA, usedB, picked = set(), set(), []
    for idx in order:
        a, b = E[idx]
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        picked.append(idx)
        if len(picked) == d:
            break
    if len(picked) < d:
        return None
    pset = set(picked)
    M2 = np.zeros((m + 1, m + 1), dtype=np.uint8)
    M2[:m, :m] = M
    x = m
    y = m
    E2 = [list(E[k]) for k in range(len(E)) if k not in pset]
    for idx in picked:
        a, b = E[idx]
        M2[a, b] = 0
        M2[x, b] = 1
        M2[a, y] = 1
        E2.append([x, b])
        E2.append([a, y])
    return M2, E2


def _anneal(M, E, rng, deadline):
    """Degree-preserving 2-switch annealing until cost 0 or deadline. Mutates M and E."""
    c = _cost(M)
    T0, T1 = 1.5, 0.2
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    L = len(E)
    while c > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        i = rng.randrange(L)
        j = rng.randrange(L)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or M[a1, b2] or M[a2, b1]:
            continue
        M[a1, b1] = 0
        M[a2, b2] = 0
        M[a1, b2] = 1
        M[a2, b1] = 1
        c2 = _cost(M)
        delta = c2 - c
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            c = c2
            E[i] = [a1, b2]
            E[j] = [a2, b1]
        else:
            M[a1, b2] = 0
            M[a2, b1] = 0
            M[a1, b1] = 1
            M[a2, b2] = 1
    return c == 0


def _grow_d3(d, graph, rng, deadline):
    """Repeatedly splice in two vertices and anneal back to diameter 3. Returns best (n, edges) or None."""
    n, edges = graph
    col = _two_colour(n, edges)
    if col is None:
        return None
    A = [v for v in range(n) if col[v] == 0]
    B = [v for v in range(n) if col[v] == 1]
    m = len(A)
    if m != len(B) or m == 0:
        return None
    ia = {v: i for i, v in enumerate(A)}
    ib = {v: i for i, v in enumerate(B)}
    M = np.zeros((m, m), dtype=np.uint8)
    E = []
    for u, v in edges:
        if col[u] == 1:
            u, v = v, u
        a, b = ia[u], ib[v]
        M[a, b] = 1
        E.append([a, b])
    if not ((M.sum(axis=0) == d).all() and (M.sum(axis=1) == d).all()):
        return None

    best = None
    while time.monotonic() < deadline:
        cand = _splice(M, E, d, rng)
        if cand is None:
            continue
        M2, E2 = cand
        now = time.monotonic()
        slice_end = min(deadline, now + max(2.0, (deadline - now) / 3.0))
        if _anneal(M2, E2, rng, slice_end):
            g = _to_graph(M2)
            if lib.is_valid(g[0], g[1], d, 3):
                best = g
                M, E = M2, E2
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    fallback = lib.haar_graph(d, range(d))
    if D != 3:
        return fallback

    # Moore-optimal case: PG(2, d-1) incidence graph.
    if lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, 3):
            return n, e

    best = fallback
    seed_g = fallback
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            al = lib.araujo_lopez_graph(d - 2)
            if lib.is_valid(al[0], al[1], d, 3):
                best = al
                seed_g = al
        except Exception:
            pass

    grown = _grow_d3(d, seed_g, rng, deadline)
    if grown is not None and grown[0] > best[0] and lib.is_valid(grown[0], grown[1], d, 3):
        best = grown

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
