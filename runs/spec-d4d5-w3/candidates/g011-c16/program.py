import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Safe baselines.
# ----------------------------------------------------------------------------

def _fallback(d):
    """K_{d,d} (diameter 2, optimal for D = 2). Valid for every D >= 2."""
    if d < 1:
        return 1, []
    return lib.haar_graph(d, range(d))


def _pg_candidate(d, D):
    """PG(2, d-1) incidence graph (Moore-optimal for D = 3) when d-1 is a prime power."""
    if D != 3:
        return None
    q = d - 1
    if q < 2 or not lib.is_prime_power(q):
        return None
    return lib.projective_plane_incidence(q)


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over a mixed family of groups, searched by simulated annealing.
#
# Layers: A_i = block i (i < k), B_j = block k + j, each block of size G.
# Slot L (of d slots) gives each A_i exactly one dart to B_{p[L][i]}, where p[L] is
# a bijection, so every B-vertex also receives d darts. Dart (L, i) with voltage s
# joins A_i,g to B_{p[L][i]}, mul(g, s), for every group element g.
# Left multiplication by a group element is an automorphism, so distances only
# need to be measured from one representative per block.
# ----------------------------------------------------------------------------

def _group_options(G, rng):
    """Return a list of (mul,) choices for groups of order G: cyclic, and Z_m x| Z_k2 variants."""
    opts = []
    try:
        _, mul, _ = lib.semidirect_group(G, 1, 1)
        opts.append(mul)
    except ValueError:
        pass
    for k2 in range(2, 13):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not cands:
            continue
        r = rng.choice(cands)
        try:
            _, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        opts.append(mul)
    return opts


def _adjacency(k, G, p, perm):
    """Adjacency lists of the lift described by slot bijections p and per-dart permutations perm."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for L in range(len(p)):
        pl = p[L]
        prow = perm[L]
        for i in range(k):
            j = pl[i]
            pm = prow[i]
            ba = i * G
            bb = (k + j) * G
            for g in range(G):
                a = ba + g
                b = bb + pm[g]
                adj[a].append(b)
                adj[b].append(a)
    return adj


def _cost(k, G, D, adj):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
    N = len(adj)
    total = 0
    for t in range(2 * k):
        src = t * G
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for w in adj[u]:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
    return total


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
    """Anneal voltages and slot bijections of a bi-Cayley lift. Returns (n, edges) or None."""
    p = []
    v = []
    perm = []
    for _ in range(d):
        p.append(rng.sample(range(k), k))
        vs = [rng.randrange(G) for _ in range(k)]
        v.append(vs)
        perm.append([[mul(g, s) for g in range(G)] for s in vs])

    adj = _adjacency(k, G, p, perm)
    cost = _cost(k, G, D, adj)
    T = 0.6

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.999)

        if rng.random() < 0.6 or k == 1:
            L = rng.randrange(d)
            i = rng.randrange(k)
            s_old = v[L][i]
            s_new = rng.randrange(G)
            if s_new == s_old:
                continue
            pm_old = perm[L][i]
            v[L][i] = s_new
            perm[L][i] = [mul(g, s_new) for g in range(G)]
            adj2 = _adjacency(k, G, p, perm)
            c2 = _cost(k, G, D, adj2)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost, adj = c2, adj2
            else:
                v[L][i] = s_old
                perm[L][i] = pm_old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            p[L][a], p[L][b] = p[L][b], p[L][a]
            adj2 = _adjacency(k, G, p, perm)
            c2 = _cost(k, G, D, adj2)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost, adj = c2, adj2
            else:
                p[L][a], p[L][b] = p[L][b], p[L][a]

    if cost != 0:
        return None
    E = set()
    N = 2 * k * G
    for L in range(d):
        for i in range(k):
            j = p[L][i]
            pm = perm[L][i]
            for g in range(G):
                a = i * G + g
                b = (k + j) * G + pm[g]
                E.add((min(a, b), max(a, b)))
    return N, sorted(E)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.82 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best_n, best_e = _fallback(d)
    if D == 2 or not lib.is_valid(best_n, best_e, d, D):
        return (best_n, best_e) if lib.is_valid(best_n, best_e, d, D) else (1, [])

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    pg = _pg_candidate(d, D)
    if pg is not None:
        consider(pg[0], pg[1])

    ks = [1, 1, 2, 2, 3, 4]
    iters = 1500 if D >= 5 else 800

    while time.monotonic() < deadline:
        k = rng.choice(ks)
        G = best_n // (2 * k) + 1 + rng.randrange(0, 2)
        if G < 2:
            G = 2
        opts = _group_options(G, rng)
        if not opts:
            continue
        mul = opts[rng.randrange(len(opts))]
        res = _anneal_lift(d, D, k, G, mul, rng, deadline, iters)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best_n, best_e, d, D):
        return _fallback(d)
    return best_n, best_e
