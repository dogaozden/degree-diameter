import math
import random
import time

import lib


def _fallback(d, D):
    """Always-valid small graph: PG(2, d-1) when D >= 3, else K_{d,d}."""
    if D >= 3 and d >= 2 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _random_regular(h, d, rng):
    """Edge keys a*h+b of a simple d-regular bipartite graph on h+h vertices (union of d matchings)."""
    for _ in range(300):
        E = set()
        ok = True
        for _layer in range(d):
            placed = False
            for _t in range(300):
                perm = list(range(h))
                rng.shuffle(perm)
                if all((a * h + perm[a]) not in E for a in range(h)):
                    placed = True
                    break
            if not placed:
                ok = False
                break
            for a in range(h):
                E.add(a * h + perm[a])
        if ok:
            return E
    return None


def _cost(h, el, D):
    """Ordered-pair count of vertex pairs at distance > D, halved (unordered). Zero means diameter <= D."""
    n = 2 * h
    adj = [[] for _ in range(n)]
    for key in el:
        a, b = divmod(key, h)
        adj[a].append(h + b)
        adj[h + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal(h, d, D, rng, deadline):
    """Edge-switch annealing on a d-regular bipartite graph with h+h vertices; returns edge keys or None."""
    E = _random_regular(h, d, rng)
    if E is None:
        return None
    el = list(E)
    S = set(E)
    cost = _cost(h, el, D)
    if cost == 0:
        return el
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    T0 = max(1.0, 0.03 * cost)
    T1 = 0.3
    m = len(el)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t_start) / span
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        old1, old2 = el[i], el[j]
        a1, b1 = divmod(old1, h)
        a2, b2 = divmod(old2, h)
        k1 = a1 * h + b2
        k2 = a2 * h + b1
        if k1 == k2 or k1 in S or k2 in S:
            continue
        el[i] = k1
        el[j] = k2
        c2 = _cost(h, el, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S.discard(old1)
            S.discard(old2)
            S.add(k1)
            S.add(k2)
            cost = c2
        else:
            el[i] = old1
            el[j] = old2
    return el if cost == 0 else None


def _to_graph(h, el):
    n = 2 * h
    edges = []
    for key in el:
        a, b = divmod(key, h)
        edges.append((a, h + b))
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget_end = start + min(0.8 * time_limit, time_limit - 8.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fb = _fallback(d, D)
    best = fb
    best_n = fb[0]
    if D <= 2 or d <= 2:
        return best if lib.is_valid(best[0], best[1], d, D) else lib.haar_graph(d, range(d))

    rng = random.Random(seed)
    M = lib.moore_bound(d, D)

    # Start the order search well above the fallback, then climb while annealing succeeds.
    h = max(best_n // 2 + 1, int(0.6 * M / 2))
    while 2 * h <= M and time.monotonic() < budget_end:
        now = time.monotonic()
        remaining = budget_end - now
        sub_deadline = now + 0.5 * remaining
        el = _anneal(h, d, D, rng, sub_deadline)
        if el is None:
            break  # could not reach this order; stop climbing
        n, edges = _to_graph(h, el)
        if n > best_n and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_n = n
        h += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
