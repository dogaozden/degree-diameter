import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Upper bound and safe baseline.
# ----------------------------------------------------------------------------

def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if d <= 0 or D <= 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    return 2 * sum((d - 1) ** i for i in range(D))


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Search family: bi-Cayley lifts over semidirect products Z_m x| Z_k2, found by
# simulated annealing with a vectorised ball-growth evaluator.
#
# Base: k A-vertices and k B-vertices. Layer l is a permutation of B-indices,
# giving d darts per A-vertex and d per B-vertex. Dart (i, j, s) joins
# A_{i,g} to B_{j, g*s} for every group element g.
#
# Left multiplication is an automorphism that is transitive on each fibre, so
# the diameter is <= D iff the ball of radius D around each of the 2k identity
# vertices covers the whole graph. The cost is the number of uncovered
# (representative, vertex) pairs; zero means valid.
# ----------------------------------------------------------------------------

_BIG = 10 ** 6


def _make_group(G, rng):
    """Return (G, table) with table[x, y] = x*y for a random Z_m x| Z_k2 of order G, or None."""
    divs = [k2 for k2 in range(1, 13) if G % k2 == 0 and G // k2 >= 2]
    rng.shuffle(divs)
    for k2 in divs:
        m = G // k2
        if k2 == 1:
            rs = [1]
        else:
            rs = [r for r in rng.sample(range(1, m), min(m - 1, 40))
                  if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not rs:
                continue
        r = rng.choice(rs)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        table = np.array([[mul(x, y) for y in range(G)] for x in range(G)], dtype=np.int64)
        return G, table
    return None


def _score(k, G, D, I, J, S, PERM, E):
    """Number of uncovered (representative, vertex) pairs after radius D. Zero means valid."""
    if len(set(zip(I, J, S))) < E:
        return _BIG  # parallel darts would create multi-edges
    K2 = 2 * k
    perms = [PERM[s] for s in S]
    cur = np.zeros((K2, K2, G), dtype=bool)
    idx = np.arange(K2)
    cur[idx, idx, 0] = True  # representative of fibre r is identity element 0
    for _ in range(D):
        nxt = cur.copy()
        for e in range(E):
            i = I[e]
            b = k + J[e]
            p = perms[e]
            nxt[:, b, p] |= cur[:, i, :]      # A_{i,g} -> B_{j,p[g]}
            nxt[:, i, :] |= cur[:, b, p]      # B_{j,p[g]} -> A_{i,g}
        cur = nxt
    return K2 * K2 * G - int(np.count_nonzero(cur))


def _anneal(d, D, k, G, PERM, rng, deadline):
    """Simulated annealing over voltages and layer targets. Returns (I, J, S) with cost 0, or None."""
    E = d * k
    I = [e % k for e in range(E)]
    J = []
    S = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        J.extend(p)
        S.extend(rng.randrange(G) for _ in range(k))
    cost = _score(k, G, D, I, J, S, PERM, E)
    it = 0
    while cost > 0:
        if time.monotonic() > deadline:
            return None
        it += 1
        T = 1.5 * (0.02 / 1.5) ** ((it % 2000) / 2000.0)  # reheating schedule
        J2 = J[:]
        S2 = S[:]
        if k > 1 and rng.random() < 0.3:
            # Swap the B-targets of two darts in one layer: keeps layers permutations.
            l = rng.randrange(d)
            a = l * k + rng.randrange(k)
            b = l * k + rng.randrange(k)
            if a == b:
                continue
            J2[a], J2[b] = J2[b], J2[a]
        else:
            S2[rng.randrange(E)] = rng.randrange(G)
        c2 = _score(k, G, D, I, J2, S2, PERM, E)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            J, S, cost = J2, S2, c2
    return I, J, S


def _edges(k, G, I, J, S, PERM):
    """Expand a base voltage assignment into the lifted (n, edges)."""
    E = set()
    for e in range(len(I)):
        p = PERM[S[e]].tolist()
        for g in range(G):
            E.add((I[e] * G + g, (k + J[e]) * G + p[g]))
    return 2 * k * G, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.82 * time_limit - 2.0)
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    mb = _moore(d, D)
    while best_n < mb and time.monotonic() < deadline:
        k = rng.choice([1, 2, 2, 3, 3, 4, 5])
        Gmin = best_n // (2 * k) + 1
        G = Gmin + rng.randrange(0, max(4, Gmin // 10 + 1))
        grp = _make_group(G, rng)
        if grp is None:
            continue
        _, table = grp
        PERM = np.ascontiguousarray(table.T)  # PERM[s][g] = g*s
        att_deadline = min(deadline, time.monotonic() + 2.0 + 3.0 * rng.random())
        res = _anneal(d, D, k, G, PERM, rng, att_deadline)
        if res is not None:
            n, e = _edges(k, G, res[0], res[1], res[2], PERM)
            consider(n, e)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
