import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe fallback: K_{d,d} (diameter 2), or K_2 when D = 1.
# ----------------------------------------------------------------------------

def _fallback(d, D):
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------
# New construction: grow-and-repair search on bipartite graphs with max degree d.
#
# State: t left vertices (indices 0..t-1) and t right vertices (indices 0..t-1),
# with an edge list E of (a, b) pairs. Left vertex a has combined id a, right
# vertex b has combined id t + b. Cost = number of unordered vertex pairs at
# distance > D (computed with bitmask BFS). Moves:
#   - add an edge between a deficient left and deficient right vertex (never
#     increases cost, so always accepted);
#   - edge switch (a,b),(c,e) -> (a,e),(c,b), which keeps all degrees fixed,
#     accepted by a time-decayed Metropolis rule.
# Growth: when a graph of size t has cost 0, add new vertex pairs, attach them
# by stealing capacity from full vertices, and repair with annealing.
# Every returned graph is checked with lib.is_valid before use.
# ----------------------------------------------------------------------------

def _cost(t, E, D):
    """Unordered pairs at distance > D in the bipartite graph with parts of size t."""
    N = 2 * t
    adj = [[] for _ in range(N)]
    for a, b in E:
        adj[a].append(t + b)
        adj[t + b].append(a)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _add_edge(E, S, deg, t, a, b):
    E.append((a, b))
    S.add((a, b))
    deg[a] += 1
    deg[t + b] += 1


def _remove_edge_at(E, S, deg, t, idx):
    a, b = E[idx]
    last = E.pop()
    if idx < len(E):
        E[idx] = last
    S.discard((a, b))
    deg[a] -= 1
    deg[t + b] -= 1


def _attach(side, v, t, E, S, deg, d, rng):
    """Give new vertex v (side 0 = left, 1 = right) degree up to d, stealing from full partners."""
    own = v if side == 0 else t + v
    for _ in range(8 * d):
        if deg[own] >= d:
            return
        w = rng.randrange(t)
        if side == 0:
            a, b = v, w
            pid = t + w
        else:
            a, b = w, v
            pid = w
        if (a, b) in S:
            continue
        if deg[pid] < d:
            _add_edge(E, S, deg, t, a, b)
            continue
        if side == 0:
            idxs = [i for i, (x, y) in enumerate(E) if y == w]
        else:
            idxs = [i for i, (x, y) in enumerate(E) if x == w]
        if not idxs:
            continue
        _remove_edge_at(E, S, deg, t, rng.choice(idxs))
        _add_edge(E, S, deg, t, a, b)


def _anneal(t, E, S, deg, d, D, rng, end):
    """Repair until cost 0 or time `end`. Returns True iff cost reached 0."""
    cur = _cost(t, E, D)
    start = time.monotonic()
    span = max(1e-6, end - start)
    T0, T1 = 1.2, 0.05
    while cur > 0:
        now = time.monotonic()
        if now >= end:
            break
        T = T0 * (T1 / T0) ** ((now - start) / span)

        defL = [a for a in range(t) if deg[a] < d]
        defR = [b for b in range(t) if deg[t + b] < d]
        if defL and defR and rng.random() < 0.5:
            a = rng.choice(defL)
            b = rng.choice(defR)
            if (a, b) not in S:
                _add_edge(E, S, deg, t, a, b)
                cur = _cost(t, E, D)   # adding an edge never increases cost
                continue

        if len(E) < 2:
            break
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or (a, e) in S or (c, b) in S:
            continue
        E[i] = (a, e)
        E[j] = (c, b)
        S.discard((a, b))
        S.discard((c, e))
        S.add((a, e))
        S.add((c, b))
        new = _cost(t, E, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            E[i] = (a, b)
            E[j] = (c, e)
            S.discard((a, e))
            S.discard((c, b))
            S.add((a, b))
            S.add((c, e))
    return cur == 0


def _grow_search(d, D, deadline, rng):
    """Grow the part size while repairing to diameter D. Returns (t, E) of the best valid state."""
    best_t = d
    best_E = [(a, b) for a in range(d) for b in range(d)]  # K_{d,d}, valid for D >= 2
    step = max(1, best_t // 4)
    while step >= 1 and time.monotonic() < deadline:
        t = best_t + step
        E = list(best_E)
        S = set(E)
        deg = [0] * (2 * t)
        for a, b in E:
            deg[a] += 1
            deg[t + b] += 1
        for v in range(best_t, t):
            _attach(0, v, t, E, S, deg, d, rng)
            _attach(1, v, t, E, S, deg, d, rng)
        remaining = deadline - time.monotonic()
        budget_end = min(deadline, time.monotonic() + max(1.5, 0.35 * remaining))
        if _anneal(t, E, S, deg, d, D, rng, budget_end):
            best_t, best_E = t, E
            step = min(2 * step, max(1, best_t // 4))
        else:
            step //= 2
    return best_t, best_E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    best = _fallback(d, D)
    if d == 1 or D <= 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Seed: projective plane incidence graph when d - 1 is a prime power (diameter 3).
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n_pg, e_pg = lib.projective_plane_incidence(d - 1)
        consider(n_pg, e_pg)

    # Main: grow-and-repair search.
    bt, bE = _grow_search(d, D, deadline, rng)
    consider(2 * bt, [(a, bt + b) for a, b in bE])

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d, D)
    return best
