import random
import time

import lib

# Change from parent: the hill-climb cost now uses vertex-transitivity of the
# Z_m lift. Translating (u, g) -> (u, g + h) is an automorphism, so the total
# number of bad pairs equals m * (sum over base vertices u of the number of
# vertices unreachable within D steps from (u, 0)). That is 2k BFS runs per
# evaluation instead of n = 2k*m, so many more voltage moves fit in the budget.


def _build_adj(k, m, darts):
    """Base adjacency for the lift: adjA[u] = [(B-base, shift)], adjB[v] = [(A-base, -shift)]."""
    adjA = [[] for _ in range(k)]
    adjB = [[] for _ in range(k)]
    for u, v, a in darts:
        adjA[u].append((v, a % m))
        adjB[v - k].append((u, (-a) % m))
    return adjA, adjB


def _bad_from(src, k, m, n, D, adjA, adjB):
    """Number of lifted vertices NOT within distance D of vertex src (a lifted id)."""
    seen = bytearray(n)
    seen[src] = 1
    frontier = [src]
    count = 1
    for _ in range(D):
        nxt = []
        for x in frontier:
            base, g = divmod(x, m)
            if base < k:
                for v, a in adjA[base]:
                    y = v * m + (g + a) % m
                    if not seen[y]:
                        seen[y] = 1
                        nxt.append(y)
            else:
                for u, a in adjB[base - k]:
                    y = u * m + (g + a) % m
                    if not seen[y]:
                        seen[y] = 1
                        nxt.append(y)
        count += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return n - count


def _cost(k, m, darts, D):
    """Zero iff the lift has diameter <= D (considering connectivity too)."""
    n = 2 * k * m
    adjA, adjB = _build_adj(k, m, darts)
    total = 0
    for base in range(2 * k):
        total += _bad_from(base * m, k, m, n, D, adjA, adjB)
    return total


def _lift_search(d, D, k, m, rng, iters, deadline):
    """Hill-climb voltages on a random d-regular bipartite base with k+k vertices.

    Returns (n, edges) with zero bad pairs, or None if the budget runs out.
    """
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]

    c = _cost(k, m, darts, D)
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        if m > 1:
            darts[j][2] = (old + rng.randrange(1, m)) % m
        c2 = _cost(k, m, darts, D)
        if c2 <= c:  # accept plateau moves too
            c = c2
        else:
            darts[j][2] = old

    if c == 0:
        n, e = lib.voltage_lift(2 * k, [tuple(x) for x in darts], m)
        return n, e
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)
    q = d - 1

    # Fallback: complete bipartite K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    # Exact extremal graph for D = 3 when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(q):
        n, e = lib.projective_plane_incidence(q)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Greedy improvement: aim one lift step above the current best size.
    ks = [1, 2, 3, 4, 6]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        m = max(2, best_n // (2 * k) + 1)
        res = _lift_search(d, D, k, m, rng, iters=3000, deadline=deadline)
        if res is not None:
            n, e = res
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n

    return best
