import math
import random
import time

import lib


try:
    (5).bit_count()

    def _pc(x):
        return x.bit_count()
except AttributeError:
    def _pc(x):
        return bin(x).count("1")


def _bad_count(N, perms, D):
    """Cost of a bipartite graph on N+N vertices given by d permutations.

    Vertex i (side A) is adjacent to N + p[i] for each permutation p. Cost is the
    number of ordered vertex pairs at distance > D, plus a penalty for duplicate
    edges (duplicates only waste degree, and the output is deduplicated).
    """
    n = 2 * N
    adj = [[] for _ in range(n)]
    seen = set()
    dup = 0
    for p in perms:
        for i in range(N):
            key = i * N + p[i]
            if key in seen:
                dup += 1
            else:
                seen.add(key)
                b = N + p[i]
                adj[i].append(b)
                adj[b].append(i)
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
    cost = sum(n - _pc(r) for r in reach)
    return cost + 4 * dup


def _edges(N, perms):
    """Deduplicated edge list of the permutation graph, vertices 0..2N-1."""
    seen = set()
    E = []
    for p in perms:
        for i in range(N):
            key = i * N + p[i]
            if key not in seen:
                seen.add(key)
                E.append((i, N + p[i]))
    return 2 * N, E


def _grow_perm(p, rng):
    """Extend a permutation of size N to size N+1 by a random transposition with the new element."""
    N = len(p)
    q = rng.randrange(N)
    new = p[:] + [N]
    new[N] = p[q]
    new[q] = N
    return new


def _anneal(d, D, N, rng, deadline, consider):
    """Simulated annealing over d permutations; grows the side size whenever diameter <= D is reached."""
    perms = [rng.sample(range(N), N) for _ in range(d)]
    cost = _bad_count(N, perms, D)
    local_best = cost
    stuck = 0
    T = 0.8
    while time.monotonic() < deadline:
        if cost == 0:
            n2, e2 = _edges(N, perms)
            consider(n2, e2)
            N += 1
            perms = [_grow_perm(p, rng) for p in perms]
            cost = _bad_count(N, perms, D)
            local_best = cost
            stuck = 0
            continue

        t = rng.randrange(d)
        p = perms[t]
        i, j = rng.sample(range(N), 2)
        p[i], p[j] = p[j], p[i]
        c2 = _bad_count(N, perms, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            p[i], p[j] = p[j], p[i]

        if cost < local_best:
            local_best = cost
            stuck = 0
        else:
            stuck += 1
            if stuck > 3000:
                # Perturb to escape a plateau.
                for _ in range(10):
                    t = rng.randrange(d)
                    p = perms[t]
                    i, j = rng.sample(range(N), 2)
                    p[i], p[j] = p[j], p[i]
                cost = _bad_count(N, perms, D)
                local_best = cost
                stuck = 0


def _araujo(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 4.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        if D >= 3:
            ap = _araujo(d)
            if ap is not None:
                consider(ap[0], ap[1])
            if d - 1 >= 2 and lib.is_prime_power(d - 1):
                pg = lib.projective_plane_incidence(d - 1)
                consider(pg[0], pg[1])

        if d >= 3 and time.monotonic() < deadline:
            # Main search: random d-regular bipartite graphs (union of d permutations),
            # annealed on the number of pairs at distance > D, growing one side at a time.
            N0 = max(2, best_n // 2 - 8)
            _anneal(d, D, N0, rng, deadline, consider)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
