import math
import random
import time

import lib

ITERS = 300  # annealing steps per random start


# ----------------------------------------------------------------------------
# Fallback families (always checked with lib.is_valid before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit lifts of a base bipartite graph with a A-vertices and a B-vertices.
#
# Vertices: A(i, x) = i*N + x and B(j, y) = a*N + j*N + y, with x, y in G.
# For each layer kk in 0..d-1 there is a permutation sig[kk] of range(a) and a
# voltage volt[kk][i] in G. Layer kk contributes the edges
#     A(i, x) -- B(sig[kk][i], x * volt[kk][i])   for all x in G.
# Each vertex gets exactly one neighbour per layer, so the graph is d-regular and
# bipartite. Left multiplication by G is an automorphism, so the diameter is at
# most D iff every base vertex A(i, 1), B(j, 1) reaches everything within D.
#
# WLOG layer 0 is the identity (relabel the B fibres), so the search only
# touches layers 1..d-1. Voltages live in a semidirect product Z_m x| Z_k.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N and Z_m x|_r Z_k well defined."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _adjacency(a, N, T, d, sig, volt):
    """Adjacency lists of the lift (duplicates are harmless for reachability)."""
    V = 2 * a * N
    adj = [[] for _ in range(V)]
    for kk in range(d):
        s = sig[kk]
        vo = volt[kk]
        for i in range(a):
            g = vo[i]
            ba = i * N
            bb = a * N + s[i] * N
            for x in range(N):
                u = ba + x
                v = bb + T[x][g]
                adj[u].append(v)
                adj[v].append(u)
    return adj


def _cost(adj, V, sources, D):
    """Total number of (source, vertex) pairs not reached within distance D."""
    total = 0
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += V - cnt
    return total


def _edges(a, N, T, d, sig, volt):
    """Edge list of the lift, deduplicated."""
    edges = set()
    for kk in range(d):
        for i in range(a):
            g = volt[kk][i]
            j = sig[kk][i]
            for x in range(N):
                edges.add((i * N + x, a * N + j * N + T[x][g]))
    return list(edges)


def _search(a, N, d, D, rng, deadline):
    """Anneal voltages and layer permutations over random groups of order N until diameter <= D."""
    groups = _groups(N)
    if not groups:
        return None
    V = 2 * a * N
    sources = [i * N for i in range(a)] + [a * N + j * N for j in range(a)]
    while time.monotonic() < deadline:
        m, k, r = rng.choice(groups)
        _, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]

        sig = [list(range(a)) for _ in range(d)]
        volt = [[0] * a for _ in range(d)]
        for kk in range(1, d):
            volt[kk] = [rng.randrange(N) for _ in range(a)]
            if a > 1:
                sig[kk] = rng.sample(range(a), a)

        cur = _cost(_adjacency(a, N, T, d, sig, volt), V, sources, D)
        for it in range(ITERS):
            if cur == 0 or time.monotonic() > deadline:
                break
            kk = rng.randrange(1, d)
            ns = [list(s) for s in sig]
            nv = [list(v) for v in volt]
            if a > 1 and rng.random() < 0.2:
                i, j = rng.sample(range(a), 2)
                ns[kk][i], ns[kk][j] = ns[kk][j], ns[kk][i]
            else:
                nv[kk][rng.randrange(a)] = rng.randrange(N)
            val = _cost(_adjacency(a, N, T, d, ns, nv), V, sources, D)
            temp = (1.0 + 0.05 * cur) * (1.0 - it / ITERS) + 0.05
            if val <= cur or rng.random() < math.exp(-(val - cur) / temp):
                sig, volt, cur = ns, nv, val

        if cur == 0:
            edges = _edges(a, N, T, d, sig, volt)
            if lib.is_valid(V, edges, d, D):
                return edges
    return None


def _configs(vmin, moore):
    """Candidate (vertices, a, N) triples with vertex count >= vmin, sorted ascending."""
    out = []
    for a in (1, 2, 3, 4):
        N0 = max(2, -(-vmin // (2 * a)))
        for N in range(N0, N0 + 6):
            V = 2 * a * N
            if vmin <= V <= moore:
                out.append((V, a, N))
    out.sort()
    return out[:16]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(0.3, 0.8 * time_limit - 1.5)

    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = 1, []

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Safe fallbacks.
    if D == 1:
        consider(2, [(0, 1)])
    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            # Record-matching case: incidence graph of PG(2, d-1).
            consider(*lib.projective_plane_incidence(d - 1))
            if D == 3:
                return best_n, best_e

    # Main search: multi-orbit lifts over semidirect products.
    if d >= 2 and D >= 2:
        moore = lib._moore_bound(d, D)
        rng = random.Random(seed)
        budget = 0.5
        while time.monotonic() < deadline:
            vmin = max(best_n + 1, (moore * 2) // 5)
            cfgs = _configs(vmin, moore)
            if not cfgs:
                break
            found = False
            for V, a, N in cfgs:
                now = time.monotonic()
                if now >= deadline:
                    break
                res = _search(a, N, d, D, rng, min(deadline, now + budget))
                if res is not None:
                    consider(V, res)
                    found = True
                    break
            if not found:
                budget *= 2

    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []
    return best_n, best_e
