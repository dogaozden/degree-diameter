import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graph: incidence graph of PG(2, q), q the largest prime power <= d - 1.
# Its vertices have spare degree d - q - 1, which the search uses for growth.
# ----------------------------------------------------------------------------

def _pg_base(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Mutable graph state: n vertices, colour (0 = A side, 1 = B side), degree list,
# edge list E of (A, B) pairs, and set S of the same pairs for membership tests.
# ----------------------------------------------------------------------------

def _add_pair(n, E, S, color, deg, d, rng):
    """Add one new A vertex and one new B vertex, each joined to deficient opposite-side vertices."""
    A_new, B_new = n, n + 1
    color.extend([0, 1])
    deg.extend([0, 0])
    def_b = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    def_a = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    rng.shuffle(def_b)
    rng.shuffle(def_a)
    for b in def_b[:d]:
        E.append((A_new, b))
        S.add((A_new, b))
        deg[A_new] += 1
        deg[b] += 1
    for a in def_a[:d]:
        E.append((a, B_new))
        S.add((a, B_new))
        deg[B_new] += 1
        deg[a] += 1
    return n + 2


def _saturate(n, E, S, color, deg, d, rng):
    """Add edges between deficient opposite-side vertices in random order. Never breaks diameter."""
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (a, b) not in S]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d and (a, b) not in S:
            E.append((a, b))
            S.add((a, b))
            deg[a] += 1
            deg[b] += 1


def _anneal(n, E, S, D, rng, deadline, iters):
    """Degree-preserving 2-switch annealing on the number of bad pairs. True if it reaches zero."""
    cost = lib.bad_pairs(n, E, D)
    for it in range(iters):
        if cost == 0:
            return True
        if time.monotonic() > deadline:
            break
        T = 1.5 * (1.0 - it / iters) + 0.2
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        e1 = (a1, b2)
        e2 = (a2, b1)
        if e1 in S or e2 in S:
            continue
        E[i] = e1
        E[j] = e2
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add(e1)
        S.add(e2)
        c2 = lib.bad_pairs(n, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            S.discard(e1)
            S.discard(e2)
            S.add((a1, b1))
            S.add((a2, b2))
    return cost == 0


def _grow_search(d, D, base, consider, rng, deadline):
    """Repeatedly add two vertices (one per side), saturate, and anneal until diameter D holds."""
    n, E0 = base
    m = n // 2
    color = [0] * m + [1] * m
    E = list(E0)
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    S = set(E)
    while time.monotonic() < deadline:
        bE = list(E)
        bS = set(S)
        bdeg = list(deg)
        bcolor = list(color)
        n2 = _add_pair(n, E, S, color, deg, d, rng)
        _saturate(n2, E, S, color, deg, d, rng)
        if _anneal(n2, E, S, D, rng, deadline, 3000):
            n = n2
            consider(n, list(E))
        else:
            E[:] = bE
            S.clear()
            S.update(bS)
            deg[:] = bdeg
            color[:] = bcolor


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
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

    if D == 3:
        # Moore-optimal case: PG(2, d-1) incidence graph is d-regular with diameter 3.
        if lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return best
        # Araujo-Pardo & Lopez record family for d-2 a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except (ValueError, StopIteration, KeyError):
                pass

    # Growth-plus-annealing from the projective plane base (diameter 3 <= D).
    pg = _pg_base(d)
    if pg is not None and D >= 3:
        consider(pg[0], pg[1])
        _grow_search(d, D, pg, consider, rng, deadline)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
