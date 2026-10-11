import math
import random
import time

import lib


def _bad_pairs(L, R, E, D):
    """Unordered pairs at distance > D in the bipartite graph with left 0..L-1, right 0..R-1 (offset L)."""
    n = L + R
    adj = [[] for _ in range(n)]
    for a, b in E:
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


def _accept(delta, T, rng):
    return delta <= 0 or rng.random() < math.exp(-delta / T)


def _anneal(L, R, E, d, D, deadline, rng):
    """Anneal edge set E (sides L, R; max degree d) to diameter <= D. Returns edge list or None."""
    E = list(E)
    Es = set(E)
    dl = [0] * L
    dr = [0] * R
    for a, b in E:
        dl[a] += 1
        dr[b] += 1
    cur = _bad_pairs(L, R, E, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        T = 0.6 + 1.5 * (1.0 - frac)
        u = rng.random()

        if u < 0.35 and len(E) >= 2:
            # Degree-preserving double edge swap.
            i = rng.randrange(len(E))
            j = rng.randrange(len(E))
            if i == j:
                continue
            a1, b1 = E[i]
            a2, b2 = E[j]
            if a1 == a2 or b1 == b2:
                continue
            n1 = (a1, b2)
            n2 = (a2, b1)
            if n1 in Es or n2 in Es:
                continue
            E[i] = n1
            E[j] = n2
            Es.discard((a1, b1)); Es.discard((a2, b2))
            Es.add(n1); Es.add(n2)
            new = _bad_pairs(L, R, E, D)
            if _accept(new - cur, T, rng):
                cur = new
            else:
                E[i] = (a1, b1)
                E[j] = (a2, b2)
                Es.discard(n1); Es.discard(n2)
                Es.add((a1, b1)); Es.add((a2, b2))

        elif u < 0.6 and E:
            # Move one endpoint on the left to a deficient left vertex.
            defl = [a for a in range(L) if dl[a] < d]
            if not defl:
                continue
            i = rng.randrange(len(E))
            a1, b1 = E[i]
            a2 = rng.choice(defl)
            if a2 == a1 or (a2, b1) in Es:
                continue
            E[i] = (a2, b1)
            Es.discard((a1, b1)); Es.add((a2, b1))
            dl[a1] -= 1; dl[a2] += 1
            new = _bad_pairs(L, R, E, D)
            if _accept(new - cur, T, rng):
                cur = new
            else:
                E[i] = (a1, b1)
                Es.discard((a2, b1)); Es.add((a1, b1))
                dl[a1] += 1; dl[a2] -= 1

        elif u < 0.85 and E:
            # Move one endpoint on the right to a deficient right vertex.
            defr = [b for b in range(R) if dr[b] < d]
            if not defr:
                continue
            i = rng.randrange(len(E))
            a1, b1 = E[i]
            b2 = rng.choice(defr)
            if b2 == b1 or (a1, b2) in Es:
                continue
            E[i] = (a1, b2)
            Es.discard((a1, b1)); Es.add((a1, b2))
            dr[b1] -= 1; dr[b2] += 1
            new = _bad_pairs(L, R, E, D)
            if _accept(new - cur, T, rng):
                cur = new
            else:
                E[i] = (a1, b1)
                Es.discard((a1, b2)); Es.add((a1, b1))
                dr[b1] += 1; dr[b2] -= 1

        else:
            # Add an edge between deficient vertices on opposite sides.
            defl = [a for a in range(L) if dl[a] < d]
            defr = [b for b in range(R) if dr[b] < d]
            if not defl or not defr:
                continue
            a = rng.choice(defl)
            b = rng.choice(defr)
            if (a, b) in Es:
                continue
            E.append((a, b))
            Es.add((a, b))
            dl[a] += 1; dr[b] += 1
            new = _bad_pairs(L, R, E, D)
            if _accept(new - cur, T, rng):
                cur = new
            else:
                E.pop()
                Es.discard((a, b))
                dl[a] -= 1; dr[b] -= 1
    return E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + max(0.5, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    # D = 3 with d - 1 a prime power: projective plane incidence is Moore-optimal.
    if D == 3 and d >= 2 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    best_n, best_e = fallback
    L = R = d
    E = [(a, b) for a in range(d) for b in range(d)]

    # Grow one vertex per side at a time; each level is annealed to diameter <= D.
    while time.monotonic() < end:
        res = _anneal(L + 1, R + 1, E, d, D, end, rng)
        if res is None:
            break
        L += 1
        R += 1
        E = res
        n = L + R
        edges = [(a, L + b) for a, b in E]
        if not lib.is_valid(n, edges, d, D):
            break
        if n > best_n:
            best_n, best_e = n, edges

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, best_e
