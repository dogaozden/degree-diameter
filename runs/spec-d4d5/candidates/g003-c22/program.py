import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Fallbacks and small-D bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: biregular bipartite graphs found by simulated annealing over
# degree-preserving 2-switches. Left vertices 0..s-1, right vertices s..2s-1.
# Each vertex has degree exactly d. The objective is the number of ordered
# vertex pairs at distance > D (zero means valid).
# ----------------------------------------------------------------------------

def _reach_masks(n, adj, D):
    """Bitmask per vertex of all vertices within distance D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _cost(n, adj, D):
    """Number of ordered pairs at distance > D (unreachable counts as bad)."""
    reach = _reach_masks(n, adj, D)
    return sum(n - r.bit_count() for r in reach)


def _adj(s, E):
    """Adjacency lists for the bipartite graph with edge list E over sides of size s."""
    adj = [[] for _ in range(2 * s)]
    for a, b in E:
        adj[a].append(s + b)
        adj[s + b].append(a)
    return adj


def _apply_swap(E, S, i, j, new_i, new_j):
    """Replace E[i], E[j] by new_i, new_j, keeping set S in sync."""
    S.discard(E[i])
    S.discard(E[j])
    E[i] = new_i
    E[j] = new_j
    S.add(new_i)
    S.add(new_j)


def _propose(E, S, rng):
    """Random 2-switch proposal: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). None if invalid."""
    m = len(E)
    i = rng.randrange(m)
    j = rng.randrange(m)
    if i == j:
        return None
    a1, b1 = E[i]
    a2, b2 = E[j]
    if a1 == a2 or b1 == b2:
        return None
    n1 = (a1, b2)
    n2 = (a2, b1)
    if n1 in S or n2 in S:
        return None
    return i, j, E[i], E[j], n1, n2


def _anneal(d, D, s, rng, t_end):
    """Anneal a d-regular bipartite graph on 2s vertices until diameter <= D or time runs out."""
    E = [(a, (a + t) % s) for a in range(s) for t in range(d)]
    S = set(E)
    for _ in range(4 * len(E)):
        p = _propose(E, S, rng)
        if p is not None:
            _apply_swap(E, S, p[0], p[1], p[4], p[5])

    n = 2 * s
    cost = _cost(n, _adj(s, E), D)
    t0 = time.monotonic()
    span = max(1e-6, t_end - t0)
    T0, T1 = 1.5, 0.05
    while cost > 0:
        now = time.monotonic()
        if now >= t_end:
            break
        frac = (now - t0) / span
        T = T0 * (T1 / T0) ** frac
        p = _propose(E, S, rng)
        if p is None:
            continue
        i, j, oi, oj, n1, n2 = p
        _apply_swap(E, S, i, j, n1, n2)
        c2 = _cost(n, _adj(s, E), D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _apply_swap(E, S, i, j, oi, oj)
    if cost == 0:
        return E
    return None


def _edges_from(s, E):
    return [(a, s + b) for a, b in E]


def _search(d, D, deadline, rng, consider):
    """Ladder search over the side size s with bisection on feasibility."""
    cap = min(400, sum((d - 1) ** i for i in range(D)))
    if cap < d + 1:
        return
    lo = d          # K_{d,d} is feasible (diameter 2)
    hi = cap + 1    # assumed infeasible beyond the cap
    s = min(cap, max(d + 1, 2 * lo))
    while time.monotonic() < deadline and lo + 1 < hi:
        remaining = deadline - time.monotonic()
        chunk = min(remaining, max(4.0, 0.3 * remaining))
        E = _anneal(d, D, s, rng, time.monotonic() + chunk)
        if E is not None:
            consider(2 * s, _edges_from(s, E))
            lo = s
            if hi == cap + 1:
                s = min(cap, 2 * s)
                if s <= lo:
                    break
                continue
        else:
            hi = s
        if lo + 1 >= hi:
            break
        s = (lo + hi) // 2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D <= 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and d >= 3:
        _search(d, D, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
