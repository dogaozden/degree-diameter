import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New family: voltage lifts of the PG(2, q) incidence graph.
#
# The base graph is the point-line incidence graph of PG(2, q) with q = d - 1.
# It is d-regular and bipartite with diameter 3. Lifting it over a group G
# gives a d-regular bipartite graph on base_n * G vertices. The lift uses the
# spare diameter (3 -> D) to allow a much larger order than the base.
#
# Lifts are searched by simulated annealing over one voltage per base edge.
# The cost counts unreached (base representative, vertex) pairs within D steps.
# Left multiplication by a group element is an automorphism of every lift, so
# only the fibre identities need to be checked as BFS sources.
# ----------------------------------------------------------------------------


def _group_table(G, rng):
    """Multiplication table of a random group of order G (cyclic or Z_m x| Z_k)."""
    opts = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if k == 1:
            opts.append(lib.cyclic_group(G)[1])
            continue
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                try:
                    opts.append(lib.semidirect_group(m, k, r)[1])
                except ValueError:
                    continue
    mul = rng.choice(opts)
    return [[mul(x, y) for y in range(G)] for x in range(G)]


def _cost(base_n, base_edges, G, T, vol, D):
    """Number of (base representative, vertex) pairs not within distance D. Zero means valid."""
    N = base_n * G
    adj = [[] for _ in range(N)]
    for (u, v), s in zip(base_edges, vol):
        ub = u * G
        vb = v * G
        for g in range(G):
            a = ub + g
            b = vb + T[g][s]
            adj[a].append(b)
            adj[b].append(a)
    ball = [1 << x for x in range(N)]
    for _ in range(D):
        new = [0] * N
        for x in range(N):
            acc = ball[x]
            for y in adj[x]:
                acc |= ball[y]
            new[x] = acc
        ball = new
    return sum(N - ball[u * G].bit_count() for u in range(base_n))


def _anneal(base_n, base_edges, G, T, D, rng, deadline, iters):
    """Anneal one voltage per base edge. Returns (cost, voltages)."""
    E = len(base_edges)
    vol = [rng.randrange(G) for _ in range(E)]
    cost = _cost(base_n, base_edges, G, T, vol, D)
    temp = 2.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(E)
        old = vol[i]
        new = rng.randrange(G)
        if new == old:
            continue
        vol[i] = new
        c = _cost(base_n, base_edges, G, T, vol, D)
        if c <= cost or rng.random() < math.exp(-(c - cost) / temp):
            cost = c
        else:
            vol[i] = old
        temp = max(0.1, temp * 0.998)
    return cost, vol


def _lift(base_n, base_edges, G, T, vol):
    """Full edge list of the lift: base vertex u, fibre g -> index u*G + g."""
    E = []
    for (u, v), s in zip(base_edges, vol):
        for g in range(G):
            E.append((u * G + g, v * G + T[g][s]))
    return base_n * G, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    q = d - 1
    if D >= 3 and q >= 2 and lib.is_prime_power(q):
        base_n, base_edges = lib.projective_plane_incidence(q)
        consider(base_n, base_edges)

        if D >= 4:
            M = lib._moore_bound(d, D)
            g_lo = max(2, int(0.4 * M / base_n))
            cands = list(range(g_lo, g_lo + 5))
            while time.monotonic() < deadline:
                G = rng.choice(cands)
                T = _group_table(G, rng)
                rdl = min(deadline, time.monotonic() + max(3.0, 0.2 * time_limit))
                cost, vol = _anneal(base_n, base_edges, G, T, D, rng, rdl, 4000)
                if cost == 0:
                    n, e = _lift(base_n, base_edges, G, T, vol)
                    consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
