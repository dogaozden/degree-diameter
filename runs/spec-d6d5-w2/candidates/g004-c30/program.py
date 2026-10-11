import math
import random
import time

import lib


def _ball_cost(n, adj, D):
    """Number of unordered vertex pairs at distance > D (0 means diameter <= D)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _random_biregular(h, d, rng):
    """Random simple d-regular bipartite edge set on sides 0..h-1 (A) and 0..h-1 (B), or None."""
    if d > h:
        return None
    for _ in range(200):
        E = set()
        ok = True
        for _layer in range(d):
            done = False
            for _t in range(300):
                p = list(range(h))
                rng.shuffle(p)
                if all((i, p[i]) not in E for i in range(h)):
                    E.update((i, p[i]) for i in range(h))
                    done = True
                    break
            if not done:
                ok = False
                break
        if ok:
            return sorted(E)
    return None


def _anneal(h, d, D, E0, rng, end):
    """Edge-swap annealing (2-switches keep degrees and bipartiteness) minimising bad pairs.

    Returns the edge list [(a, b)] with a, b in 0..h-1 (B side offset by h applied by caller), or None.
    """
    n = 2 * h
    el = [tuple(e) for e in E0]
    S = set(el)
    m = len(el)

    def cost_of(cur_el):
        adj = [[] for _ in range(n)]
        for a, b in cur_el:
            adj[a].append(h + b)
            adj[h + b].append(a)
        return _ball_cost(n, adj, D)

    cur = cost_of(el)
    t0 = time.monotonic()
    total = max(1e-6, end - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= end:
            return None
        T = 1.5 * (1.0 - (now - t0) / total) + 0.05
        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = el[i]
        a2, b2 = el[j]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in S or n2 in S:
            continue
        el[i] = n1
        el[j] = n2
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add(n1)
        S.add(n2)
        c2 = cost_of(el)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
        else:
            el[i] = (a1, b1)
            el[j] = (a2, b2)
            S.discard(n1)
            S.discard(n2)
            S.add((a1, b1))
            S.add((a2, b2))
    return el


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if d == 2:
        N = 2 * D
        consider(N, [(i, (i + 1) % N) for i in range(N)])
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # Algebraic seeds for D >= 3 (diameter 3 constructions also satisfy larger D).
    if D >= 3:
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Main search: random d-regular bipartite graphs on h + h vertices, annealed
    # by edge swaps to diameter <= D. Sizes increase after each success.
    ok_h = max(d, best_n // 2)
    step = max(1, ok_h // 40)
    while time.monotonic() < deadline:
        h_try = ok_h + step
        E = _random_biregular(h_try, d, rng)
        if E is None:
            step += 1
            continue
        remaining = deadline - time.monotonic()
        if remaining <= 0.5:
            break
        budget = min(remaining, max(3.0, 0.25 * remaining))
        el = _anneal(h_try, d, D, E, rng, time.monotonic() + budget)
        if el is not None:
            consider(2 * h_try, [(a, h_try + b) for a, b in el])
            ok_h = h_try
            step = max(1, ok_h // 40)
        else:
            step = max(1, step // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
