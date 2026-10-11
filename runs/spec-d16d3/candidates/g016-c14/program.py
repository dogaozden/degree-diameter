import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines.
# ----------------------------------------------------------------------------

def _kdd(d):
    """K_{d,d}: diameter 2, valid for every D >= 2."""
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


def _pg_baseline(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over non-abelian groups, annealed for diameter D.
#
# Groups: G = Z_m x| Z_k2 (semidirect product, k2 = 1 gives the cyclic group).
# Base: k "A-classes" and k "B-classes". Class i of A has vertices A_{i,g}, g in G,
# class j of B has vertices B_{j,h}. For each (i,j) a set S_ij of shifts with
# |S_ij| = M[i][j] gives edges A_{i,g} ~ B_{j, g*s} for s in S_ij.
# Left multiplication by any element is an automorphism, so distances from
# A_{i,e} and B_{j,e} to all vertices determine the diameter. Cost = number of
# unreached (source, vertex) pairs within distance D over the 2k sources.
# The degree of every vertex is d when all row and column sums of M equal d.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul_table) for a random group of order G, or None."""
    ks = [k2 for k2 in (1, 2, 3, 4, 5, 6, 8) if G % k2 == 0 and G // k2 >= 2]
    if not ks:
        return None
    k2 = rng.choice(ks)
    m = G // k2
    if k2 == 1:
        r = 1
    else:
        cands = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
    try:
        order, mulf, _ = lib.semidirect_group(m, k2, r)
    except ValueError:
        return None
    mul = [[mulf(x, y) for y in range(order)] for x in range(order)]
    return order, mul


def _init_adj(k, G, mul, S):
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i in range(k):
        for j in range(k):
            bj = k * G + j * G
            for s in S[i][j]:
                for g in range(G):
                    a = i * G + g
                    b = bj + mul[g][s]
                    adj[a].append(b)
                    adj[b].append(a)
    return adj


def _set_shift(k, G, mul, adj, i, j, old, new):
    """Replace shift old by new in cell (i, j), updating adjacency lists in place."""
    bj = k * G + j * G
    for g in range(G):
        a = i * G + g
        bo = bj + mul[g][old]
        bn = bj + mul[g][new]
        adj[a].remove(bo)
        adj[bo].remove(a)
        adj[a].append(bn)
        adj[bn].append(a)


def _cost(k, G, adj, D):
    """Total unreached (source, vertex) pairs within distance D; 0 means diameter <= D."""
    N = 2 * k * G
    sources = [i * G for i in range(k)] + [k * G + j * G for j in range(k)]
    total = 0
    for src in sources:
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
        total += N - cnt
    return total


def _anneal(k, G, mul, M, D, rng, deadline, iters):
    """Simulated annealing over the connection sets. Returns S (k x k lists of shifts) or None."""
    cells = [(i, j) for i in range(k) for j in range(k) if M[i][j] > 0]
    S = [[[] for _ in range(k)] for _ in range(k)]
    for i, j in cells:
        S[i][j] = rng.sample(range(G), M[i][j])
    adj = _init_adj(k, G, mul, S)
    cost = _cost(k, G, adj, D)
    T0 = max(1.0, 0.03 * cost)
    T1 = 0.25
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (t / iters)
        i, j = cells[rng.randrange(len(cells))]
        lst = S[i][j]
        idx = rng.randrange(len(lst))
        old = lst[idx]
        new = rng.randrange(G)
        if new in lst:
            continue
        _set_shift(k, G, mul, adj, i, j, old, new)
        c2 = _cost(k, G, adj, D)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
            lst[idx] = new
            cost = c2
        else:
            _set_shift(k, G, mul, adj, i, j, new, old)
    return S if cost == 0 else None


def _edges_from(k, G, mul, S):
    E = []
    for i in range(k):
        for j in range(k):
            bj = k * G + j * G
            for s in S[i][j]:
                for g in range(G):
                    E.append((i * G + g, bj + mul[g][s]))
    return 2 * k * G, E


def _search(d, D, best, deadline, rng, moore):
    """Anneal bi-Cayley graphs over random groups, returning the best valid (n, edges) found."""
    while time.monotonic() < deadline and best[0] < moore:
        ks = [k for k in (1, 2) if best[0] // (2 * k) + 1 <= moore // (2 * k)]
        if not ks:
            break
        k = rng.choice(ks)
        G_min = best[0] // (2 * k) + 1
        G_max = moore // (2 * k)
        G = min(G_max, G_min + rng.randrange(0, 4))
        grp = _sample_group(G, rng)
        if grp is None:
            continue
        order, mul = grp
        if k == 1:
            M = [[d]]
        else:
            a = rng.randint(1, d - 1)
            M = [[a, d - a], [d - a, a]]
        S = _anneal(k, order, mul, M, D, rng, deadline, iters=4000)
        if S is not None:
            n, E = _edges_from(k, order, mul, S)
            if n > best[0] and lib.is_valid(n, E, d, D):
                best = (n, E)
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 0.5
    rng = random.Random(seed * 1000003 + d * 31 + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _kdd(d)  # safe fallback for D >= 2
    moore = lib._moore_bound(d, D)

    if D >= 3:
        pg = _pg_baseline(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

    if best[0] >= moore or D < 3 or d < 2:
        return best

    try:
        best = _search(d, D, best, deadline, rng, moore)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = _kdd(d)
    return best
