import math
import random
import time

import numpy as np

import lib


def _colour(n, adj):
    """Two-colour a bipartite graph given as adjacency lists (iterative DFS from each unseen vertex)."""
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
    return col


def _oriented(n, edges):
    """Return edges as [colour0, colour1] pairs, plus the colouring."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = _colour(n, adj)
    return [[u, v] if col[u] == 0 else [v, u] for u, v in edges]


def _bad(M, N):
    """Ordered count of off-diagonal pairs at distance > 3, via walks of length 1..3 on a dense 0/1 matrix.

    Any walk of length <= 3 gives a path of length <= 3, so this is exact for D = 3.
    Zero means the graph has diameter <= 3 (on a connected graph).
    """
    A2 = M @ M
    A3 = A2 @ M
    R = (M + A2 + A3) > 0.5
    np.fill_diagonal(R, True)
    return int(N * N - np.count_nonzero(R))


def _grow(n, E, d, rng, t_end):
    """Add a point P and a line L (two new vertices) by degree-preserving edge switches, then anneal.

    Starting state: d disjoint edges (a_i, b_i) are replaced by (a_i, P) and (b_i, L), so every old
    vertex keeps degree d and P, L get degree d. Annealing applies 2-switches (a,b),(c,e) -> (a,e),(c,b),
    which keep degrees and bipartiteness, and minimises the number of pairs at distance > 3.
    Returns (n+2, edges) with diameter <= 3, or None if no valid state is reached before t_end.
    """
    N = n + 2
    P, L = n, n + 1  # P has colour 1, L has colour 0

    order = list(range(len(E)))
    rng.shuffle(order)
    used, pick = set(), []
    for idx in order:
        a, b = E[idx]
        if a not in used and b not in used:
            pick.append(idx)
            used.add(a)
            used.add(b)
            if len(pick) == d:
                break
    if len(pick) < d:
        return None

    picked = set(pick)
    E2 = [list(E[i]) for i in range(len(E)) if i not in picked]
    for idx in pick:
        a, b = E[idx]
        E2.append([a, P])
        E2.append([L, b])

    M = np.zeros((N, N), dtype=np.float32)
    for a, b in E2:
        M[a, b] = 1.0
        M[b, a] = 1.0

    cur = _bad(M, N)
    start = time.monotonic()
    span = max(t_end - start, 1e-3)
    M_edges = len(E2)
    while cur > 0:
        now = time.monotonic()
        if now >= t_end:
            return None
        frac = (now - start) / span
        T = 0.4 * (1.0 - frac) + 0.02

        i = rng.randrange(M_edges)
        j = rng.randrange(M_edges)
        if i == j:
            continue
        a, b = E2[i]
        c, e = E2[j]
        if a == c or b == e or M[a, e] or M[c, b]:
            continue

        # Apply 2-switch: (a,b),(c,e) -> (a,e),(c,b)
        M[a, b] = M[b, a] = 0.0
        M[c, e] = M[e, c] = 0.0
        M[a, e] = M[e, a] = 1.0
        M[c, b] = M[b, c] = 1.0
        new = _bad(M, N)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E2[i] = [a, e]
            E2[j] = [c, b]
        else:
            M[a, e] = M[e, a] = 0.0
            M[c, b] = M[b, c] = 0.0
            M[a, b] = M[b, a] = 1.0
            M[c, e] = M[e, c] = 1.0

    return N, [(int(x), int(y)) for x, y in E2]


def _base(d, D):
    """Structured base for D = 3, or None."""
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)  # order 2(q^2+q+1), degree q+1
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)      # order 2(q^2+q+5), degree q+2 = d
    return None


def _haar_fallback(d, D, rng, deadline):
    """Random Haar graphs with growing modulus; K_{d,d} is the always-valid starting point."""
    best = lib.haar_graph(d, range(d))
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    best = None
    try:
        base = _base(d, D)
        if base is not None and lib.is_valid(base[0], base[1], d, D):
            best = base
            if D == 3:
                E = _oriented(best[0], best[1])
                mb = lib._moore_bound(d, D)
                while time.monotonic() < deadline and best[0] + 2 <= mb:
                    now = time.monotonic()
                    budget = 0.5 * (deadline - now)
                    res = _grow(best[0], E, d, rng, now + budget)
                    if res is None or not lib.is_valid(res[0], res[1], d, D):
                        break
                    best = res
                    E = _oriented(best[0], best[1])
    except Exception:
        best = None

    if best is None:
        best = _haar_fallback(d, D, rng, deadline)

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
