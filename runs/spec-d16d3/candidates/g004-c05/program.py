import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_options(G):
    """(k, r) choices for groups of order G: k = 1 is the cyclic group, otherwise Z_m x| Z_k with m = G // k."""
    opts = [(1, 1)]
    for k in range(2, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((k, r))
    return opts


def _tables(G, k, r):
    """Full multiplication table M and inverse list I for the chosen group. Identity is element 0."""
    if k == 1:
        _, mul, inv = lib.cyclic_group(G)
    else:
        _, mul, inv = lib.semidirect_group(G // k, k, r)
    M = [[mul(x, y) for y in range(G)] for x in range(G)]
    I = [inv(x) for x in range(G)]
    return M, I


def _cost_sets(S, G, M, I):
    """Diameter-3 cost for a bi-Cayley graph over G with connection set S.

    Same-side pairs need S S^-1 = G and S^-1 S = G. Cross pairs then follow automatically.
    """
    IS = [I[t] for t in S]
    aa = set()
    bb = set()
    for s in S:
        Ms = M[s]
        Is = M[I[s]]
        for t, it in zip(S, IS):
            aa.add(Ms[it])
            bb.add(Is[t])
    return 2 * G - len(aa) - len(bb)


def _cost_bfs(S, G, D, M, I):
    """General-D cost: unreached vertices within distance D from A_e and B_e (vertex transitivity per side)."""
    N = 2 * G
    IS = [I[s] for s in S]
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    Mu = M[u]
                    for s in S:
                        v = G + Mu[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    Mh = M[u - G]
                    for s in IS:
                        v = Mh[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
    return total


def _cost(S, G, D, M, I):
    if D == 3:
        return _cost_sets(S, G, M, I)
    return _cost_bfs(S, G, D, M, I)


def _anneal(G, d, D, M, I, rng, deadline, slice_len):
    """Time-scheduled annealing over d-subsets of the group. Returns S with zero cost, or None."""
    t0 = time.monotonic()
    S = rng.sample(range(G), d)
    inS = [False] * G
    for x in S:
        inS[x] = True
    cost = _cost(S, G, D, M, I)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline or now - t0 >= slice_len:
            return None
        T = 1.0 * (0.02 ** ((now - t0) / slice_len)) + 1e-9
        i = rng.randrange(d)
        new = rng.randrange(G)
        if inS[new]:
            continue
        old = S[i]
        S[i] = new
        c2 = _cost(S, G, D, M, I)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
            inS[old] = False
            inS[new] = True
            cost = c2
        else:
            S[i] = old
    return list(S)


def _edges_k1(G, S, M):
    """Bi-Cayley graph: A_g = g, B_h = G + h, and A_g ~ B_{g s} for s in S."""
    E = []
    for g in range(G):
        Mg = M[g]
        for s in S:
            E.append((g, G + Mg[s]))
    return 2 * G, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best_n = 2 * d
    best_e = [(i, d + j) for i in range(d) for j in range(d)]

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main family: bi-Cayley graphs over groups of order G with one vertex per side.
    # Such a graph has 2G vertices and is d-regular. Its diameter is at most D iff
    # the connection set S (|S| = d) satisfies the covering conditions described in _cost_sets.
    moore = lib._moore_bound(d, D)
    Gmax = min(moore // 2, 600)
    G = max(d, best_n // 2 + 1)
    rng = random.Random(seed * 1000003 + 97 * d + D)

    while G <= Gmax and time.monotonic() < deadline:
        opts = _group_options(G)
        done = False
        while not done and time.monotonic() < deadline:
            k, r = rng.choice(opts)
            M, I = _tables(G, k, r)
            S = _anneal(G, d, D, M, I, rng, deadline, slice_len=3.0)
            if S is not None:
                n, e = _edges_k1(G, S, M)
                consider(n, e)
                done = True
        if not done:
            break
        G += 1

    if not lib.is_valid(best_n, best_e, d, D):
        best_n = 2 * d
        best_e = [(i, d + j) for i in range(d) for j in range(d)]
    return best_n, best_e
