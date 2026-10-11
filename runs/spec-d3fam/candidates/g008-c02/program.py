import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Adjacency-set helpers.
# ----------------------------------------------------------------------------

def _to_sets(n, edges):
    nbr = [set() for _ in range(n)]
    for u, v in edges:
        nbr[u].add(v)
        nbr[v].add(u)
    return nbr


def _to_edges(nbr):
    return [(a, b) for a in range(len(nbr)) for b in nbr[a] if a < b]


def _two_colour(nbr):
    n = len(nbr)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in nbr[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


# ----------------------------------------------------------------------------
# New idea: paired vertex insertion by edge subdivision, then degree-preserving
# double-edge-swap annealing that drives the diameter defect to zero.
#
# Insertion: pick d edges (a_i, b_i) with distinct a_i and distinct b_i. Replace
# each (a_i, b_i) by (a_i, y) and (x, b_i), where x is a new A-side vertex and y
# a new B-side vertex. Old degrees are unchanged, and x and y each gain d
# neighbours. Double-edge swaps then keep every degree fixed while searching for
# a pattern with diameter <= D. Cost = number of ordered unreachable pairs.
# ----------------------------------------------------------------------------

def _cost(nbr, D):
    """Ordered pairs at distance > D (0 means diameter <= D and connected)."""
    n = len(nbr)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _insert_pair(nbr, col, d, rng):
    """Append new vertices x (side 0) and y (side 1), each with up to d neighbours by subdivision."""
    n = len(nbr)
    x, y = n, n + 1
    nbr.append(set())
    nbr.append(set())
    col.append(0)
    col.append(1)
    cand = [(a, b) for a in range(n) if col[a] == 0 for b in nbr[a]]
    rng.shuffle(cand)
    used_a = set()
    used_b = set()
    got = 0
    for a, b in cand:
        if got >= d:
            break
        if a in used_a or b in used_b:
            continue
        nbr[a].discard(b)
        nbr[b].discard(a)
        nbr[a].add(y)
        nbr[y].add(a)
        nbr[b].add(x)
        nbr[x].add(b)
        used_a.add(a)
        used_b.add(b)
        got += 1
    return x, y


def _anneal(nbr, col, D, deadline, rng):
    """Degree-preserving double-edge-swap annealing. True if cost reaches 0 before deadline."""
    E = [[a, b] for a in range(len(nbr)) if col[a] == 0 for b in nbr[a]]
    if len(E) < 2:
        return False
    cost = _cost(nbr, D)
    if cost == 0:
        return True
    T0, T1 = 4.0, 0.1
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while True:
        now = time.monotonic()
        if now >= deadline:
            return False
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or b2 in nbr[a1] or b1 in nbr[a2]:
            continue
        nbr[a1].remove(b1)
        nbr[b1].remove(a1)
        nbr[a2].remove(b2)
        nbr[b2].remove(a2)
        nbr[a1].add(b2)
        nbr[b2].add(a1)
        nbr[a2].add(b1)
        nbr[b1].add(a2)
        c2 = _cost(nbr, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            E[i] = [a1, b2]
            E[j] = [a2, b1]
            cost = c2
            if cost == 0:
                return True
        else:
            nbr[a1].remove(b2)
            nbr[b2].remove(a1)
            nbr[a2].remove(b1)
            nbr[b1].remove(a2)
            nbr[a1].add(b1)
            nbr[b1].add(a1)
            nbr[a2].add(b2)
            nbr[b2].add(a2)


def _grow_by_insertion(n, edges, d, D, deadline, rng):
    """Repeatedly insert a vertex pair and anneal; keep each success, discard failures."""
    nbr = _to_sets(n, edges)
    col = _two_colour(nbr)
    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        attempt_end = min(deadline, now + max(1.0, 0.6 * (deadline - now)))
        nb = [set(s) for s in nbr]
        cl = list(col)
        _insert_pair(nb, cl, d, rng)
        if _anneal(nb, cl, D, attempt_end, rng):
            nbr, col = nb, cl
    return len(nbr), _to_edges(nbr)


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _largest_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if D == 2:
        return fallback

    best = fallback

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    base = None
    if D == 3 and lib.is_prime_power(d - 1):
        # Moore-optimal: PG(2, d-1) incidence graph is d-regular with diameter 3.
        return lib.projective_plane_incidence(d - 1)

    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            base = lib.araujo_lopez_graph(d - 2)
        except (ValueError, StopIteration, KeyError):
            base = None

    if base is None:
        base = _largest_pg(d)

    if base is None:
        return fallback

    consider(base[0], base[1])

    # New search: grow the base by paired vertex insertion plus annealing.
    n2, e2 = _grow_by_insertion(base[0], base[1], d, D, deadline, rng)
    consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
