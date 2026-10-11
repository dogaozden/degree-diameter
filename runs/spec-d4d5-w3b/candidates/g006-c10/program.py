import math
import random
import time

import lib


def _cost(L, edges, D):
    """Number of unordered vertex pairs at distance > D in the bipartite graph with sides 0..L-1 and L..2L-1."""
    n = 2 * L
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(L + b)
        adj[L + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal(L, edges, D, rng, deadline, cap):
    """Edge-switch annealing on a d-regular bipartite graph; returns zero-cost edges or None."""
    edges = [list(e) for e in edges]
    eset = {(a, b) for a, b in edges}
    cur = _cost(L, edges, D)
    if cur == 0:
        return [tuple(e) for e in edges]
    t_start = time.monotonic()
    t_stop = min(deadline, t_start + cap)
    span = max(1e-9, t_stop - t_start)
    T0, T1 = 1.5, 0.12
    m = len(edges)
    while True:
        now = time.monotonic()
        if now >= t_stop:
            break
        frac = (now - t_start) / span
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = edges[i]
        a2, b2 = edges[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        eset.discard((a1, b1))
        eset.discard((a2, b2))
        eset.add((a1, b2))
        eset.add((a2, b1))
        edges[i] = [a1, b2]
        edges[j] = [a2, b1]
        new = _cost(L, edges, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
            cur = new
            if cur == 0:
                return [tuple(e) for e in edges]
        else:
            eset.discard((a1, b2))
            eset.discard((a2, b1))
            eset.add((a1, b1))
            eset.add((a2, b2))
            edges[i] = [a1, b1]
            edges[j] = [a2, b2]
    return None


def _grow(L, edges, d, rng):
    """Add one vertex per side: remove a random d-matching and reattach its endpoints to the new vertices."""
    order = list(range(len(edges)))
    rng.shuffle(order)
    used_a, used_b = set(), set()
    chosen = []
    for idx in order:
        a, b = edges[idx]
        if a in used_a or b in used_b:
            continue
        chosen.append(idx)
        used_a.add(a)
        used_b.add(b)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    chosen_set = set(chosen)
    new_edges = [e for k, e in enumerate(edges) if k not in chosen_set]
    for idx in chosen:
        a, b = edges[idx]
        new_edges.append((a, L))
        new_edges.append((L, b))
    return L + 1, new_edges


def _search(d, D, seed, deadline):
    """Grow a d-regular bipartite graph level by level, repairing diameter by annealing."""
    rng = random.Random(seed)
    bound = lib.moore_bound(d, D)
    L = d
    edges = [(i, j) for i in range(d) for j in range(d)]  # K_{d,d}
    best = (L, list(edges))
    attempt_cap = 6.0
    while time.monotonic() < deadline:
        g = _grow(L, edges, d, rng)
        if g is None:
            break
        NL, gedges = g
        if 2 * NL > bound:
            break
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            break
        res = _anneal(NL, gedges, D, rng, deadline, min(attempt_cap, remaining))
        if res is not None:
            L, edges = NL, list(res)
            best = (L, list(edges))
            attempt_cap = 6.0
        else:
            attempt_cap = min(attempt_cap * 1.3, 30.0)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    candidates = [fallback]

    if D == 2:
        return fallback

    if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        try:
            candidates.append(lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    try:
        deadline = start + max(0.5, 0.82 * time_limit)
        L, local_edges = _search(d, D, seed, deadline)
        n = 2 * L
        edges = [(a, L + b) for a, b in local_edges]
        candidates.append((n, edges))
    except Exception:
        pass

    best = fallback
    for cand in sorted(candidates, key=lambda c: -c[0]):
        try:
            if lib.is_valid(cand[0], cand[1], d, D):
                best = cand
                break
        except Exception:
            continue
    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
