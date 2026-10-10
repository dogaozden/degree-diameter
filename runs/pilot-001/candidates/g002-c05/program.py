import math
import random
import time

import lib


def _moore(d, D):
    """Bipartite Moore bound for max degree d and diameter D (no cap for d <= 2)."""
    if d <= 2:
        return 10 ** 9
    return 2 * sum((d - 1) ** i for i in range(D))


def _adj_lift(k, m, d, sig, volt):
    """Adjacency sets of the Z_m lift of a bipartite base with k+k vertices and d darts per A-vertex.

    A-vertex (u, g) has index u*m+g; B-vertex (v, h) has index (k+v)*m+h.
    Dart i at u goes to B-vertex sig[i][u] with voltage volt[i][u].
    """
    n = 2 * k * m
    adj = [set() for _ in range(n)]
    for u in range(k):
        for g in range(m):
            x = u * m + g
            for i in range(d):
                y = (k + sig[i][u]) * m + (g + volt[i][u]) % m
                adj[x].add(y)
                adj[y].add(x)
    return adj


def _bad(k, m, d, D, sig, volt):
    """Number of ordered (source, target) pairs not within distance D, using base-vertex sources.

    The lift is invariant under translation of Z_m, so sources (x, 0) for every base vertex x
    cover all pairs.
    """
    n = 2 * k * m
    adj = _adj_lift(k, m, d, sig, volt)
    total = 0
    for s in range(2 * k):
        src = s * m
        seen = [False] * n
        seen[src] = True
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for x in frontier:
                for y in adj[x]:
                    if not seen[y]:
                        seen[y] = True
                        nxt.append(y)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += n - cnt
    return total


def _search(k, m, d, D, rng, iters, deadline):
    """Anneal voltages and permutations until the lift has diameter <= D or budget runs out.

    Worsening moves are accepted with a Boltzmann probability under a geometrically cooling
    temperature, so the search can escape plateaus that pure hill climbing gets stuck on.
    The best state seen is returned.
    """
    sig = [rng.sample(range(k), k) for _ in range(d)]
    volt = [[rng.randrange(m) for _ in range(k)] for _ in range(d)]
    cur = _bad(k, m, d, D, sig, volt)
    best_bad, best_sig, best_volt = cur, sig, volt
    temp = max(1.0, 0.1 * cur)
    decay = 0.98
    for _ in range(iters):
        if best_bad == 0 or time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        u = rng.randrange(k)
        s2 = [r[:] for r in sig]
        v2 = [r[:] for r in volt]
        if k > 1 and rng.random() < 0.5:
            u2 = rng.randrange(k)
            s2[i][u], s2[i][u2] = s2[i][u2], s2[i][u]
            v2[i][u], v2[i][u2] = v2[i][u2], v2[i][u]
        else:
            v2[i][u] = rng.randrange(m)
        new = _bad(k, m, d, D, s2, v2)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            sig, volt, cur = s2, v2, new
            if cur < best_bad:
                best_bad, best_sig, best_volt = cur, sig, volt
        temp = max(1e-9, temp * decay)
    return best_bad == 0, best_sig, best_volt


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.7 * time_limit, time_limit - 3.0))
    deadline = start + budget

    if d <= 0:
        return 1, []
    if D <= 1:
        return 2, [(0, 1)]

    # Safe fallback: complete bipartite K_{d,d} (diameter 2, valid for D >= 2).
    fallback = lib.haar_graph(d, range(d))

    # Optimal construction when D = 3 and d-1 is a prime power.
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        cand = lib.projective_plane_incidence(q)
        if lib.is_valid(cand[0], cand[1], d, D):
            return cand

    rng = random.Random(seed)
    moore = _moore(d, D)
    best_n = 0
    best = None

    # Voltage lifts of random bipartite base graphs with k+k vertices,
    # searched by annealing over permutations and voltages.
    for k in range(1, 400):
        if time.monotonic() >= deadline:
            break
        m = 2
        fails = 0
        while time.monotonic() < deadline:
            n = 2 * k * m
            if n > moore:
                break
            ok, sig, volt = _search(k, m, d, D, rng, 200, deadline)
            if ok:
                if n > best_n:
                    best_n = n
                    best = (k, m, sig, volt)
                m += 1
                fails = 0
            else:
                fails += 1
                if fails >= 2:
                    break

    if best is None:
        return fallback

    k, m, sig, volt = best
    n = 2 * k * m
    adj = _adj_lift(k, m, d, sig, volt)
    edges = [(x, y) for x in range(n) for y in adj[x] if x < y]
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return fallback
