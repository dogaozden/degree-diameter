import math
import random
import time

import lib


def _anneal(n, E, Es, D, rng, deadline, iters):
    """Edge 2-switch annealing on the bipartite edge list E (pairs (a, b), a in A, b in B).

    A 2-switch keeps every degree fixed. Cost is the number of vertex pairs at distance > D.
    Mutates E and Es in place. Returns the final cost (0 means valid).
    """
    cost = lib.bad_pairs(n, E, D)
    if cost == 0 or len(E) < 2:
        return cost
    T0 = 0.5 + 0.1 * cost
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - it / iters) + 0.05
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in Es or (a2, b1) in Es:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        Es.discard((a1, b1))
        Es.discard((a2, b2))
        Es.add((a1, b2))
        Es.add((a2, b1))
        c2 = lib.bad_pairs(n, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            Es.discard((a1, b2))
            Es.discard((a2, b1))
            Es.add((a1, b1))
            Es.add((a2, b2))
    return cost


def _grow_by_insertion(d, D, n, E, deadline, rng, best):
    """Repeatedly insert two new vertices (one per side) and re-anneal to diameter D.

    Insertion removes a matching of d edges (a_i, b_i) and adds x-b_i and a_i-y, where x is a
    new A-vertex and y a new B-vertex. Every degree stays the same, so the result is d-regular.
    """
    moore = lib._moore_bound(d, D)
    Es = set(E)
    while time.monotonic() < deadline and n < moore:
        order = list(range(len(E)))
        rng.shuffle(order)
        usedA, usedB, chosen = set(), set(), []
        for idx in order:
            a, b = E[idx]
            if a in usedA or b in usedB:
                continue
            usedA.add(a)
            usedB.add(b)
            chosen.append(idx)
            if len(chosen) == d:
                break
        if len(chosen) < d:
            continue
        pairs = [E[idx] for idx in chosen]
        removed = set(pairs)
        E2 = [e for e in E if e not in removed]
        Es2 = Es - removed
        x, y = n, n + 1
        for a, b in pairs:
            E2.append((x, b))
            E2.append((a, y))
            Es2.add((x, b))
            Es2.add((a, y))
        n2 = n + 2
        cost = _anneal(n2, E2, Es2, D, rng, deadline, 400)
        if cost == 0 and lib.is_valid(n2, E2, d, D):
            n, E, Es = n2, E2, Es2
            if n > best[0]:
                best = (n, list(E))
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # Always-valid fallback: K_{d,d} has diameter 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    # Projective plane incidence graph meets the Moore bound when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        pg = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(pg[0], pg[1], d, D):
            return pg

    best = fallback
    try:
        n0, E0 = fallback
        best = _grow_by_insertion(d, D, n0, list(E0), deadline, rng, best)
    except Exception:
        pass

    n, E = best
    E = [(int(u), int(v)) for u, v in E]
    if not lib.is_valid(n, E, d, D):
        return fallback
    return n, E
