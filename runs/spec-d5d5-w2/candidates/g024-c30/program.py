import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Warm-started edge-switching annealing for d-regular bipartite graphs.
#
# State: a d-regular bipartite graph with N vertices per side, stored as a list
# of pairs (a, b) with a in 0..N-1 (side A) and b in 0..N-1 (side B). The
# output vertex for b is N + b. Growth inserts one A and one B vertex at a time
# (removing d edges and rewiring them through the new vertices), which keeps
# the graph d-regular. Annealing then applies degree-preserving edge switches,
# minimising the number of ordered vertex pairs at distance greater than D.
# A state is accepted only when that cost reaches zero. The last valid state is
# kept as the warm start for the next growth step.
# ----------------------------------------------------------------------------


def _to_graph(N, edges):
    return 2 * N, [(a, N + b) for a, b in edges]


def _adj_from(N, edges):
    adj = [[] for _ in range(2 * N)]
    for a, b in edges:
        adj[a].append(N + b)
        adj[N + b].append(a)
    return adj


def _cost(n, adj, D):
    """Number of ordered pairs (v, w) with distance > D, via bitset balls."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt[v] = x
        ball = nxt
    return sum(n - x.bit_count() for x in ball)


def _move(N, adj, edges, eset, i, a, b):
    """Replace edge i with (a, b), keeping adj and eset consistent."""
    oa, ob = edges[i]
    adj[oa].remove(N + ob)
    adj[N + ob].remove(oa)
    eset.discard((oa, ob))
    edges[i] = (a, b)
    adj[a].append(N + b)
    adj[N + b].append(a)
    eset.add((a, b))


def _insert_pair(N, edges, d, rng):
    """Add one A vertex and one B vertex, keeping d-regularity. Returns (N+1, edges) or None."""
    order = list(range(len(edges)))
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
    chosen_set = set(chosen)
    na = N
    nb = N
    new = [edges[k] for k in range(len(edges)) if k not in chosen_set]
    for idx in chosen:
        a, b = edges[idx]
        new.append((a, nb))
        new.append((na, b))
    return N + 1, new


def _anneal(N, edges, d, D, rng, deadline):
    """Edge-switch annealing. Returns a valid edge list or None if the deadline passes."""
    edges = list(edges)
    eset = set(edges)
    adj = _adj_from(N, edges)
    n = 2 * N
    m = len(edges)
    cost = _cost(n, adj, D)
    if cost == 0:
        return edges
    T0 = max(2.0, 0.02 * cost)
    T1 = 0.3
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while True:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = edges[i]
        a2, b2 = edges[j]
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        _move(N, adj, edges, eset, i, a1, b2)
        _move(N, adj, edges, eset, j, a2, b1)
        c2 = _cost(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost == 0:
                return edges
        else:
            _move(N, adj, edges, eset, j, a2, b2)
            _move(N, adj, edges, eset, i, a1, b1)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    moore = lib.moore_bound(d, D)

    # Safe fallback: K_{d,d}, diameter 2 (valid for every D >= 2).
    kdd = [(a, b) for a in range(d) for b in range(d)]
    best_n, best_e = _to_graph(d, kdd)
    state_N, state = d, kdd

    # D = 3 structured start: incidence graph of PG(2, d-1), d-regular, diameter 3.
    if D == 3:
        q = d - 1
        if q >= 2 and lib.is_prime_power(q):
            n, e = lib.projective_plane_incidence(q)
            if n > best_n and lib.is_valid(n, e, d, D):
                m = n // 2
                best_n, best_e = n, e
                state_N, state = m, [(u, v - m) for u, v in e]

    # Grow from the current valid state, annealing after each growth step.
    step = max(1, state_N // 30)
    while time.monotonic() < deadline and best_n < moore:
        max_side = moore // 2
        if state_N >= max_side:
            break
        s = min(step, max_side - state_N)
        cand_N, cand = state_N, state
        for _ in range(s):
            res = _insert_pair(cand_N, cand, d, rng)
            if res is None:
                break
            cand_N, cand = res
        if cand_N == state_N:
            step = 1
            continue

        remaining = deadline - time.monotonic()
        if remaining <= 0:
            break
        slice_end = min(deadline, time.monotonic() + max(1.0, 0.2 * remaining))
        out = _anneal(cand_N, cand, d, D, rng, slice_end)
        if out is not None:
            state_N, state = cand_N, out
            n, e = _to_graph(state_N, state)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_e = n, e
        else:
            step = max(1, step // 2)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = _to_graph(d, kdd)
    return best_n, best_e
