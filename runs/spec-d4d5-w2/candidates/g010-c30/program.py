import math
import random
import time

import lib


def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _cost(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs count)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _replace(E, adj, S, idx, na, nb, h):
    """Set edge idx to (na, nb), keeping adjacency lists and the edge set in sync.
    A-vertices are 0..h-1, B-vertices are h..2h-1 in adj."""
    oa, ob = E[idx]
    adj[oa].remove(h + ob)
    adj[h + ob].remove(oa)
    S.discard((oa, ob))
    E[idx] = (na, nb)
    adj[na].append(h + nb)
    adj[h + nb].append(na)
    S.add((na, nb))


def _anneal(d, D, h, rng, deadline):
    """Start from a Haar graph (d-regular, bipartite) on h + h vertices and anneal
    over bipartiteness-preserving, degree-preserving double edge swaps,
    minimising the number of bad pairs. Returns (n, edges) on success, else None."""
    n = 2 * h
    shifts = rng.sample(range(h), d)
    E = []
    S = set()
    adj = [[] for _ in range(n)]
    for a in range(h):
        for s in shifts:
            b = (a + s) % h
            E.append((a, b))
            S.add((a, b))
            adj[a].append(h + b)
            adj[h + b].append(a)
    m = len(E)
    cost = _cost(n, adj, D)
    T0 = max(1.0, 0.03 * cost)
    T1 = 0.1
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    frac = 0.0
    it = 0
    while cost > 0:
        if (it & 15) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = min(1.0, (now - t0) / span)
        it += 1
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        _replace(E, adj, S, i, a1, b2, h)
        _replace(E, adj, S, j, a2, b1, h)
        c2 = _cost(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _replace(E, adj, S, i, a1, b1, h)
            _replace(E, adj, S, j, a2, b2, h)
    if cost != 0:
        return None
    return n, [(a, h + b) for a, b in E]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 3.0))
    deadline = start + budget

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    kdd = [(i, d + j) for i in range(d) for j in range(d)]
    if D == 2:
        return 2 * d, kdd
    if d == 2:
        n = 2 * D  # even cycle C_{2D} has diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, then the projective plane incidence graph if it is larger.
    best_n, best_e = 2 * d, kdd
    try:
        pg = _pg_fallback(d)
        if pg is not None and pg[0] > best_n and lib.is_valid(pg[0], pg[1], d, D):
            best_n, best_e = pg
    except Exception:
        pass

    if best_n >= lib.moore_bound(d, D):
        return best_n, best_e

    # Bold direction: direct local search over bipartite d-regular graphs.
    # Each target size h (per side) is annealed from scratch; success raises the bar.
    rng = random.Random(seed * 1000003 + 97 * d + D)
    try:
        best_h = best_n // 2
        fails = 0
        step = max(1, best_h // 25)
        while time.monotonic() < deadline and fails < 3:
            h = best_h + step
            now = time.monotonic()
            remaining = deadline - now
            run_dl = min(deadline, now + max(2.0, 0.5 * remaining))
            res = _anneal(d, D, h, rng, run_dl)
            if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
                best_n, best_e = res
                best_h = best_n // 2
                step = max(1, best_h // 25)
                fails = 0
            else:
                if step > 1:
                    step = 1
                else:
                    fails += 1
    except Exception:
        pass

    try:
        if not lib.is_valid(best_n, best_e, d, D):
            return 2 * d, kdd
    except Exception:
        return 2 * d, kdd
    return best_n, best_e
