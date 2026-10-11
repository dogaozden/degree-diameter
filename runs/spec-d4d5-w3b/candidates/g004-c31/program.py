"""Annealed growth of d-regular bipartite graphs from a projective-plane base.

Start from a valid d-regular bipartite graph (PG(2, d-1) incidence when d-1 is a
prime power, otherwise K_{d,d}). Repeatedly:
  1. Anneal with degree-preserving double-edge swaps to minimise the number of
     vertex pairs at distance > D.
  2. When the cost reaches 0, record the graph and grow it by one vertex per side.
     Growth removes d pairwise-disjoint edges (a_i, b_i) and attaches a new A vertex
     to every b_i and a new B vertex to every a_i. Degrees stay exactly d.

Every returned graph is checked with lib.is_valid, with K_{d,d} as the fallback.
"""
import math
import random
import time

import lib


def _base(d, D):
    """Return (N, local_edges) for a d-regular bipartite base graph with N vertices per side."""
    if D >= 3 and d >= 3 and lib.is_prime_power(d - 1):
        n2, edges = lib.projective_plane_incidence(d - 1)
        m = n2 // 2
        return m, [(u, v - m) for u, v in edges]
    return d, [(a, b) for a in range(d) for b in range(d)]


def _to_graph(N, E):
    """Global (n, edges): A vertices are 0..N-1, B vertices are N..2N-1."""
    return 2 * N, [(a, N + b) for a, b in E]


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _cost(N, E, D):
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    return _bad(n, adj, D)


def _anneal(N, E, S, D, rng, deadline, iters):
    """Metropolis search over double-edge swaps (preserve all degrees). Returns final cost."""
    cost = _cost(N, E, D)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add((a1, b2))
        S.add((a2, b1))
        c2 = _cost(N, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            S.discard((a1, b2))
            S.discard((a2, b1))
            S.add((a1, b1))
            S.add((a2, b2))
        T = max(0.2, T * 0.9995)
    return cost


def _grow(N, E, S, d, rng):
    """Add one A and one B vertex, keeping every degree equal to d. Returns (N+1, E) or None."""
    idx = list(range(len(E)))
    rng.shuffle(idx)
    used_a, used_b, pick = set(), set(), []
    for k in idx:
        a, b = E[k]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        pick.append(k)
        if len(pick) == d:
            break
    if len(pick) < d:
        return None
    picked = set(pick)
    newE = [e for k, e in enumerate(E) if k not in picked]
    for k in pick:
        a, b = E[k]
        S.discard((a, b))
    na, nb = N, N
    for k in pick:
        a, b = E[k]
        newE.append((na, b))
        newE.append((a, nb))
        S.add((na, b))
        S.add((a, nb))
    return N + 1, newE


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.80 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    best = fallback
    try:
        N, E = _base(d, D)
        cand = _to_graph(N, E)
        if lib.is_valid(cand[0], cand[1], d, D) and cand[0] > best[0]:
            best = cand
        # Calibration shortcut: already at the Moore bound, nothing to gain.
        if lib.moore_bound(d, D) <= best[0]:
            return best

        rng = random.Random(seed)
        S = set(E)
        while time.monotonic() < deadline:
            cost = _anneal(N, E, S, D, rng, deadline, iters=4000)
            if cost != 0:
                continue
            n_c, e_c = _to_graph(N, E)
            if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)
            res = _grow(N, E, S, d, rng)
            if res is None:
                break
            N, E = res
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
