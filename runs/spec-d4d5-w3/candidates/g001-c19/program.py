import math
import random
import time

import lib


def _bad(k, E, D):
    """Number of unordered vertex pairs at distance > D in the bipartite graph with sides 0..k-1 (A) and k..2k-1 (B)."""
    n = 2 * k
    nb = [[] for _ in range(n)]
    for a, b in E:
        nb[a].append(k + b)
        nb[k + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _graft(k, E, d, rng):
    """Add one A-vertex and one B-vertex to a d-regular bipartite graph, keeping it d-regular and bipartite."""
    if len(E) < d:
        return None
    idx = None
    for _ in range(300):
        cand = rng.sample(range(len(E)), d)
        A = [E[i][0] for i in cand]
        B = [E[i][1] for i in cand]
        if len(set(A)) == d and len(set(B)) == d:
            idx = cand
            break
    if idx is None:
        return None
    drop = set(idx)
    newE = [e for t, e in enumerate(E) if t not in drop]
    newE += [(k, b) for b in B]   # new A vertex k joins the old B endpoints
    newE += [(a, k) for a in A]   # new B vertex k joins the old A endpoints
    return k + 1, newE


def _search(k, E, d, D, rng, deadline):
    """Anneal double-edge swaps (keeps d-regularity and bipartiteness) until all pairs are within D.

    Returns (k, E) on success, or None at the deadline. E is mutated in place.
    """
    S = {a * k + b for a, b in E}
    cost = _bad(k, E, D)
    L = 3000
    T_hi, T_lo = 1.0, 0.1
    while True:
        if cost == 0:
            return k, E
        if time.monotonic() > deadline:
            return None
        for t in range(L):
            if t % 64 == 0 and time.monotonic() > deadline:
                return None
            T = T_hi * (T_lo / T_hi) ** (t / L)
            i = rng.randrange(len(E))
            j = rng.randrange(len(E))
            if i == j:
                continue
            a1, b1 = E[i]
            a2, b2 = E[j]
            if a1 == a2 or b1 == b2:
                continue
            n1 = a1 * k + b2
            n2 = a2 * k + b1
            if n1 in S or n2 in S:
                continue
            E[i] = (a1, b2)
            E[j] = (a2, b1)
            S.discard(a1 * k + b1)
            S.discard(a2 * k + b2)
            S.add(n1)
            S.add(n2)
            c2 = _bad(k, E, D)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
                if cost == 0:
                    return k, E
            else:
                E[i] = (a1, b1)
                E[j] = (a2, b2)
                S.discard(n1)
                S.discard(n2)
                S.add(a1 * k + b1)
                S.add(a2 * k + b2)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 1.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = (2 * d, [(a, d + b) for a in range(d) for b in range(d)])
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])
        if not lib.is_valid(2, [(0, 1)], d, D):
            return 1, []

    rng = random.Random(seed)

    # Base: incidence graph of PG(2, d-1) when d-1 is a prime power (d-regular, diameter 3).
    if D >= 3 and d >= 3 and lib.is_prime_power(d - 1):
        n2, edges = lib.projective_plane_incidence(d - 1)
        k = n2 // 2
        E = [(u, v - k) for u, v in edges]
        if lib.is_valid(n2, edges, d, D) and n2 > best[0]:
            best = (n2, edges)
    else:
        k = d
        E = [(a, b) for a in range(d) for b in range(d)]

    # Ladder: anneal at the current order, record each success, then graft to a larger order.
    while time.monotonic() < deadline:
        out = _search(k, E, d, D, rng, deadline)
        if out is None:
            break
        k, E = out
        n = 2 * k
        edges = [(a, k + b) for a, b in E]
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
        g = _graft(k, E, d, rng)
        if g is None:
            break
        k, E = g

    if not lib.is_valid(best[0], best[1], d, D):
        best = (2 * d, [(a, d + b) for a in range(d) for b in range(d)])
    return best
