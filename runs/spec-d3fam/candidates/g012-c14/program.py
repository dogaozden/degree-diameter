import math
import random
import time

import numpy as np

import lib

_ITERS = 2000
_T0 = 3.0
_T1 = 0.3


def _orient(n, edges):
    """Orient each edge so its first endpoint has colour 0 in a BFS 2-colouring."""
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
    return [(u, v) if col[u] == 0 else (v, u) for u, v in edges]


def _regular(n, edges, d):
    """True if every vertex has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


def _bad_count(N, M, D):
    """Number of unordered pairs at distance > D. (I+A)^D has a positive entry iff distance <= D."""
    B = M.copy()
    np.fill_diagonal(B, 1.0)
    P = B
    for _ in range(D - 1):
        P = P @ B
    return int(np.count_nonzero(P == 0)) // 2


def _twin_insert(N, edges, d, rng):
    """Degree-preserving vertex-pair insertion.

    Remove a random matching of d edges (a_i, b_i), add a new side-0 vertex v joined to
    all b_i and a new side-1 vertex w joined to all a_i. Every degree stays d.
    """
    E = len(edges)
    order = list(range(E))
    rng.shuffle(order)
    used_a, used_b, chosen = set(), set(), []
    for idx in order:
        a, b = edges[idx]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        chosen.append(idx)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    cs = set(chosen)
    v, w = N, N + 1
    out = [edges[i] for i in range(E) if i not in cs]
    for idx in chosen:
        a, b = edges[idx]
        out.append((a, w))
        out.append((v, b))
    return out


def _anneal_edges(N, edges, D, rng, deadline, iters):
    """Simulated annealing over degree-preserving double-edge swaps, minimising bad pairs."""
    E = [tuple(e) for e in edges]
    M = np.zeros((N, N))
    for a, b in E:
        M[a, b] = 1.0
        M[b, a] = 1.0
    eset = set(E)
    cost = _bad_count(N, M, D)
    m = len(E)
    for it in range(iters):
        if cost == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        T = _T0 * (_T1 / _T0) ** (it / max(1, iters))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        M[a1, b1] = M[b1, a1] = 0.0
        M[a2, b2] = M[b2, a2] = 0.0
        M[a1, b2] = M[b2, a1] = 1.0
        M[a2, b1] = M[b1, a2] = 1.0
        c2 = _bad_count(N, M, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            eset.discard((a1, b1))
            eset.discard((a2, b2))
            eset.add((a1, b2))
            eset.add((a2, b1))
            E[i] = (a1, b2)
            E[j] = (a2, b1)
        else:
            M[a1, b2] = M[b2, a1] = 0.0
            M[a2, b1] = M[b1, a2] = 0.0
            M[a1, b1] = M[b1, a1] = 1.0
            M[a2, b2] = M[b2, a2] = 1.0
    return cost, E


def _twin_search(n0, e0, d, D, rng, deadline):
    """Repeatedly insert a vertex pair and repair with annealing; keep only zero-cost results."""
    cur_n, cur_e = n0, e0
    while time.monotonic() < deadline:
        trial = _twin_insert(cur_n, cur_e, d, rng)
        if trial is None:
            break
        c, E2 = _anneal_edges(cur_n + 2, trial, D, rng, deadline, _ITERS)
        if c == 0:
            cur_n += 2
            cur_e = E2
    return cur_n, cur_e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d}: d-regular, diameter 2, optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    bases = [best]
    if d - 1 >= 2 and lib.is_prime_power(d - 1):
        bases.append(lib.projective_plane_incidence(d - 1))
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            bases.append(lib.araujo_lopez_graph(d - 2))
        except ValueError:
            pass
    bases = [b for b in bases
             if _regular(b[0], b[1], d) and lib.is_valid(b[0], b[1], d, D)]
    base = max(bases, key=lambda b: b[0])

    if base[0] >= lib._moore_bound(d, D):
        return base

    best = base
    n_b = base[0]
    e_b = _orient(n_b, base[1])
    n_f, e_f = _twin_search(n_b, e_b, d, D, rng, deadline)
    cand = (n_f, [tuple(e) for e in e_f])
    if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
        best = cand
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
