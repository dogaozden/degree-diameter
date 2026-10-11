import math
import random
import time

import lib


def _group_options(N, cache):
    """All semidirect products Z_m x|_r Z_k of order N (cyclic when r = 1), as (m, k, r) triples."""
    if N in cache:
        return cache[N]
    opts = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    cache[N] = opts
    return opts


def _fiber_bad(N, mul, a, darts, D):
    """Fiber-transitive diameter test.

    The lift of a base multigraph on 2a vertices by a group G of order N has automorphisms
    (u, x) -> (u, h*x) for every h in G, so every vertex is equivalent to a fiber representative
    (u, identity). Hence the diameter is <= D iff every representative reaches all vertices
    within D steps. Returns the number of (representative, vertex) pairs at distance > D.
    """
    V = 2 * a * N
    adj = [[] for _ in range(V)]
    for u, v, g in darts:
        for x in range(N):
            p = u * N + x
            q = v * N + mul(x, g)
            adj[p].append(q)
            adj[q].append(p)
    bad = 0
    for rep in range(2 * a):
        s = rep * N              # identity element is index 0 in lib.semidirect_group
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for p in frontier:
                for q in adj[p]:
                    if not seen[q]:
                        seen[q] = 1
                        nxt.append(q)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        bad += V - count
    return bad


def _climb(N, mul, a, darts, D, rng, steps, deadline):
    """Hill climb on voltages: minimise the count of far pairs; sideways moves are allowed."""
    bad = _fiber_bad(N, mul, a, darts, D)
    for _ in range(steps):
        if bad == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(len(darts))
        u, v, g = darts[i]
        darts[i] = (u, v, rng.randrange(N))
        nb = _fiber_bad(N, mul, a, darts, D)
        if nb <= bad:
            bad = nb
        else:
            darts[i] = (u, v, g)
    return bad


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(1.0, 0.8 * time_limit - 2.0)

    if d < 1 or D < 1:
        return 1, []

    # Exact projective-plane record when it applies (d-1 a prime power, D = 3).
    qq = d - 1
    if D == 3 and d >= 3 and lib.is_prime_power(qq):
        n, e = lib.projective_plane_incidence(qq)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Trivially valid fallback: a single edge.
    best_n, best_e = 2, [(0, 1)]
    moore = lib.moore_bound(d, D)
    rng = random.Random(seed)
    cache = {}

    # Search over bi-Cayley lifts of d-regular bipartite base multigraphs on a + a vertices,
    # with voltages in non-abelian (semidirect) groups of order N.
    while time.monotonic() < deadline:
        if best_n >= moore:
            break
        a = rng.choice((1, 1, 1, 2, 2, 3))
        top = moore // (2 * a)
        lo = best_n // (2 * a) + 1
        if lo > top:
            continue
        span = top - lo
        if rng.random() < 0.5:
            N = lo + rng.randrange(min(6, span + 1))
        else:
            N = lo + int(rng.random() ** 2 * (span + 1))
        N = min(N, top)

        opts = _group_options(N, cache)
        if not opts:
            continue
        m, k, r = rng.choice(opts)
        _, mul, _ = lib.semidirect_group(m, k, r)

        # Base multigraph: d random perfect matchings between A = {0..a-1} and B = {a..2a-1}.
        darts = []
        for _ in range(d):
            perm = list(range(a))
            rng.shuffle(perm)
            for i in range(a):
                darts.append((i, a + perm[i], rng.randrange(N)))

        bad = _climb(N, mul, a, darts, D, rng, steps=600, deadline=deadline)
        if bad != 0:
            continue

        n = 2 * a * N
        if n <= best_n:
            continue
        edge_set = set()
        for u, v, g in darts:
            for x in range(N):
                p = u * N + x
                q2 = v * N + mul(x, g)
                edge_set.add((min(p, q2), max(p, q2)))
        edges = sorted(edge_set)
        if lib.is_valid(n, edges, d, D):
            best_n, best_e = n, edges

    return best_n, best_e
