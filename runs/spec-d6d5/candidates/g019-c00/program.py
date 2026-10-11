import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley (k = 1) search over groups, a different family from the parent's
# multi-base annealing.
#
# Vertices: A_g = g (0..G-1) and B_h = G + h. Connection set S of size d in a
# group of order G gives edges A_g -- B_{g*s} for s in S. Left multiplication
# by any group element is an automorphism, and it is transitive on A and on B
# separately. So diameter <= D holds iff A_e and B_e both reach every vertex
# within D steps. Each cost evaluation is therefore only two bounded BFS runs.
# ----------------------------------------------------------------------------


def _sample_group(G, rng):
    """Return (order, mul, inv) for a random group of order G: a semidirect product
    Z_m x| Z_k with k >= 2 when possible, otherwise the cyclic group Z_G."""
    divs = [k for k in range(2, G + 1) if G % k == 0 and G // k >= 3]
    if divs and rng.random() < 0.8:
        for _ in range(20):
            k = rng.choice(divs)
            m = G // k
            for _ in range(200):
                r = rng.randrange(2, m)
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    return lib.semidirect_group(m, k, r)
    return lib.semidirect_group(G, 1, 1)


def _make_eval(G, mul, inv):
    """Build (cost, edges) closures for a group of order G with multiplication mul and inverse inv."""
    cache = {}

    def col(s):
        c = cache.get(s)
        if c is None:
            c = [mul(g, s) for g in range(G)]
            cache[s] = c
        return c

    def build_adj(S):
        Rs = [col(s) for s in S]
        Ri = [col(inv(s)) for s in S]
        adj = [[G + c[g] for c in Rs] for g in range(G)]
        adj += [[c[h] for c in Ri] for h in range(G)]
        return adj

    def missing(adj, src, D):
        """Number of vertices not reached from src within D steps."""
        N = 2 * G
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        return N - cnt

    def cost(S, D):
        adj = build_adj(S)
        return missing(adj, 0, D) + missing(adj, G, D)

    def edges(S):
        return [(g, G + col(s)[g]) for s in S for g in range(G)]

    return cost, edges


def _climb(d, G, cost, D, rng, deadline):
    """Simulated-annealing style search over d-subsets of the group. Returns S with cost 0 or None."""
    S = rng.sample(range(G), d)
    c = cost(S, D)
    T = 1.0
    while c > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T2 = S[:]
        T2[i] = x
        c2 = cost(T2, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / max(T, 1e-3)):
            S, c = T2, c2
        T = max(0.05, T * 0.9995)
    return S if c == 0 else None


def _pg_candidate(d):
    """Incidence graph of PG(2, d-1) when d-1 is a prime power (Moore graph for D = 3)."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 3.0))
    deadline = t0 + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback

    try:
        pg = _pg_candidate(d)
        if pg is not None and lib.is_valid(pg[0], pg[1], d, D):
            if D == 3:
                return pg  # Moore graph: optimal for D = 3
            if pg[0] > best[0]:
                best = pg
    except Exception:
        pass

    rng = random.Random(seed)
    try:
        while time.monotonic() < deadline:
            G = best[0] // 2 + 1 + rng.randrange(3)
            G = max(G, d, 2)
            order, mul, inv = _sample_group(G, rng)
            if order < d:
                continue
            cost, edges_fn = _make_eval(order, mul, inv)
            attempt_deadline = min(deadline, time.monotonic() + 8.0)
            S = _climb(d, order, cost, D, rng, attempt_deadline)
            if S is None:
                continue
            n = 2 * order
            E = edges_fn(S)
            if n > best[0] and lib.is_valid(n, E, d, D):
                best = (n, E)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
