import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Unstructured search: regular bipartite graphs with annealed double edge swaps.
#
# State: s vertices per side, a d-regular simple bipartite graph given by the
# edge list E of pairs (a, b), a in [0, s), b in [0, s). Vertex ids in the
# combined graph are a (side A) and s + b (side B).
#
# Cost: number of ordered vertex pairs at distance > D (zero means valid).
# Moves preserve regularity and bipartiteness. When a level reaches cost zero,
# the graph is expanded by one vertex per side with a degree-preserving splice
# and annealing continues at the larger size.
# ----------------------------------------------------------------------------

def _adj(s, E):
    adj = [[] for _ in range(2 * s)]
    for a, b in E:
        adj[a].append(s + b)
        adj[s + b].append(a)
    return adj


def _bad(N, adj, D):
    """Ordered pairs (v, w) with dist(v, w) > D, computed with bitmask balls."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(N - bin(r).count("1") for r in reach)


def _anneal(s, E, D, rng, deadline):
    """Anneal E in place toward diameter <= D. Returns E on success, else None."""
    Es = set(E)
    N = 2 * s
    cost = _bad(N, _adj(s, E), D)
    if cost == 0:
        return E
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    T0, T1 = 3.0, 0.3
    m = len(E)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - t_start) / span)
        T = T0 * (T1 / T0) ** frac

        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if (a1, b2) in Es or (a2, b1) in Es:
            continue

        Es.discard((a1, b1))
        Es.discard((a2, b2))
        Es.add((a1, b2))
        Es.add((a2, b1))
        E[i] = (a1, b2)
        E[j] = (a2, b1)

        c2 = _bad(N, _adj(s, E), D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            Es.discard((a1, b2))
            Es.discard((a2, b1))
            Es.add((a1, b1))
            Es.add((a2, b2))
            E[i] = (a1, b1)
            E[j] = (a2, b2)

    return E if cost == 0 else None


def _expand(d, s, E, rng):
    """Add one vertex per side, keeping d-regularity, by splicing d disjoint edges.

    Each chosen edge (x, y) is replaced by (new_A, y) and (x, new_B). Chosen
    edges have pairwise distinct endpoints so the result is simple.
    Returns (s + 1, new_E) or None if no suitable matching was found.
    """
    idx = list(range(len(E)))
    rng.shuffle(idx)
    used_a, used_b, chosen = set(), set(), []
    for k in idx:
        a, b = E[k]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        chosen.append(k)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    rem = set(chosen)
    newE = [e for k, e in enumerate(E) if k not in rem]
    for k in chosen:
        x, y = E[k]
        newE.append((s, y))   # new A vertex to old B vertex y
        newE.append((x, s))   # old A vertex x to new B vertex
    return s + 1, newE


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    fallback = (2 * d, [(a, d + b) for a in range(d) for b in range(d)])
    best = fallback

    # Fast path: projective plane incidence meets the Moore bound for D = 3.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, edges = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, edges, d, D):
            return n, edges

    rng = random.Random(seed * 1000003 + d * 131 + D)

    try:
        s = d
        E = [(a, b) for a in range(d) for b in range(d)]
        while time.monotonic() < deadline:
            res = _anneal(s, E, D, rng, deadline)
            if res is None:
                break
            edges = [(a, s + b) for a, b in res]
            if not lib.is_valid(2 * s, edges, d, D):
                break
            best = (2 * s, edges)
            nxt = _expand(d, s, res, rng)
            if nxt is None:
                break
            s, E = nxt
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
