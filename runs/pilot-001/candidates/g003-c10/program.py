import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D.

    Cost = number of vertex pairs at distance > D. Returns S with cost 0, or None.
    """
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:  # accept sideways moves to escape plateaus
            S, c = T, ct
    return S if c == 0 else None


def _search_lift(d, D, k, m, rng, iters, deadline, warm=None):
    """Hill-climb Z_m voltages on a d-regular bipartite base with k+k vertices.

    If `warm` (a list of darts from an earlier successful search with the same k)
    is given, the search starts from those darts (voltages reduced mod m) instead
    of a random base. Returns (n, edges, darts) with zero bad pairs, or None.
    """
    if warm is None:
        perms = [rng.sample(range(k), k) for _ in range(d)]
        darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]
    else:
        darts = [[u, v, a % m] for u, v, a in warm]

    def evaluate():
        n, e = lib.voltage_lift(2 * k, [tuple(x) for x in darts], m)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0:
            break
        if time.monotonic() > deadline:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        if m > 1:
            darts[j][2] = (old + rng.randrange(1, m)) % m
        n2, e2, c2 = evaluate()
        if c2 <= c:  # accept plateau moves too
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return n, e, [tuple(x) for x in darts]
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # D = 3: projective plane with largest prime power q <= d - 1.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Mixed search: Haar graphs with growing modulus, and voltage lifts.
    # Lifts are warm-started: the last successful darts for each base size k
    # seed the next attempt at a larger modulus, so progress accumulates
    # instead of restarting from random voltages.
    haar_m, haar_miss = d + 1, 0
    warm = {}  # k -> darts of the most recent successful lift
    while time.monotonic() < deadline:
        if rng.random() < 0.5 and haar_miss < 4:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
        else:
            k = rng.choice([1, 2, 3, 4])
            m = max(2, best_n // (2 * k) + 1)
            w = warm.get(k)
            res = _search_lift(d, D, k, m, rng, 200, deadline, warm=w)
            if res is None and w is not None:
                # Warm start failed; fall back to a fresh random search.
                res = _search_lift(d, D, k, m, rng, 200, deadline)
            if res is not None:
                consider(res[0], res[1])
                warm[k] = res[2]

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
