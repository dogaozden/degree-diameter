import random
import time

import lib

# New idea: random biregular bipartite base multigraph + Z_m voltage lift,
# with voltages found by hill-climbing on the number of bad pairs (pairs at
# distance > D). The base is the sum of d random permutation matrices on k+k
# vertices, so every base vertex has degree d. Each dart (A_i -> B_j, voltage a)
# lifts to a perfect matching-like shift of size m. The k = 1 case is a Haar
# graph with hill-climbed shifts; larger k gives more base-vertex freedom.


def _lift_search(d, D, k, m, rng, iters, deadline):
    """Hill-climb voltages on a random d-regular bipartite base with k+k vertices.

    Returns (n, edges) with zero bad pairs, or None if the budget runs out.
    """
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]

    def evaluate(ds):
        n, e = lib.voltage_lift(2 * k, [tuple(x) for x in ds], m)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate(darts)
    for _ in range(iters):
        if c == 0:
            break
        if time.monotonic() > deadline:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        if m > 1:
            darts[j][2] = (old + rng.randrange(1, m)) % m
        n2, e2, c2 = evaluate(darts)
        if c2 <= c:  # accept plateau moves too
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return n, e
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)
    q = d - 1

    # Fallback: complete bipartite K_{d,d}, always valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    # Exact extremal graph for D = 3 when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(q):
        n, e = lib.projective_plane_incidence(q)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Greedy improvement: aim one lift step above the current best size.
    ks = [1, 2, 3, 4]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        m = max(2, best_n // (2 * k) + 1)
        res = _lift_search(d, D, k, m, rng, iters=200, deadline=deadline)
        if res is not None:
            n, e = res
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n

    return best
