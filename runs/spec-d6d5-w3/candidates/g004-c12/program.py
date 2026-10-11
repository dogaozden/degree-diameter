import math
import random
import time

import numpy as np

import lib

_BIG = 10 ** 6


# ----------------------------------------------------------------------------
# Small-D baselines: projective plane incidence and Araujo-Pardo-Lopez (D = 3).
# ----------------------------------------------------------------------------

def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2, q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New family for D >= 5: bi-Cayley-type voltage lifts over non-abelian groups.
#
# Group G = Z_m x| Z_k (order G). There are k "A-orbits" and k "B-orbits".
# Layer L (L = 0..d-1) has a permutation P[L] of range(k) and voltages V[L][i].
# A_{i,g} is joined to B_{P[L][i], g * V[L][i]} for every layer L.
# Each A and each B vertex then has degree d.
#
# Left multiplication by h is an automorphism, so the graph is determined up to
# isomorphism by distances from A_{i,e} and B_{j,e}. Diameter <= D is therefore
# checked with 2k bounded BFS runs over numpy arrays, which is far cheaper than
# a full all-pairs check.
# ----------------------------------------------------------------------------

def _group_tables(G, rng):
    """Random semidirect product Z_m x| Z_k of order G.

    Returns (R, inv): R[s, g] = index of g*s, inv[s] = index of s^-1. Identity is index 0.
    """
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    for _ in range(40):
        k = rng.choice(divs)
        m = G // k
        if k == 1:
            r = 1
        else:
            cands = [x for x in range(1, m)
                     if math.gcd(x, m) == 1 and pow(x, k, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
        s = np.arange(G, dtype=np.int64)
        sa, sb = s // k, s % k
        # mul((a,b),(c,d)) = ((a + r^b c) mod m, (b + d) mod k)
        R = (((sa[None, :] + pw[sb][None, :] * sa[:, None]) % m) * k
             + (sb[None, :] + sb[:, None]) % k)
        nb = (-sb) % k
        inv = ((-pw[nb] * sa) % m) * k + nb
        return R.astype(np.int64), inv.astype(np.int64)
    return None


def _has_dup(P, V, k):
    """True if two layers would give the same edge (same B-target and voltage from one A)."""
    for i in range(k):
        seen = set()
        for L in range(len(P)):
            key = (P[L][i], V[L][i])
            if key in seen:
                return True
            seen.add(key)
    return False


def _unreached(ADJ, total, src, D):
    """Number of vertices not within distance D of src."""
    seen = np.zeros(total, dtype=bool)
    seen[src] = True
    frontier = np.array([src], dtype=np.int64)
    for _ in range(D):
        nb = ADJ[frontier].ravel()
        nb = np.unique(nb[~seen[nb]])
        if nb.size == 0:
            break
        seen[nb] = True
        frontier = nb
    return total - int(np.count_nonzero(seen))


def _cost(R, inv, G, k, D, P, V):
    """Number of (source, vertex) pairs left uncovered; zero means diameter <= D."""
    if _has_dup(P, V, k):
        return _BIG
    d = len(P)
    M = k * G
    ADJ = np.empty((2 * M, d), dtype=np.int64)
    for L in range(d):
        for i in range(k):
            j = P[L][i]
            s = V[L][i]
            ADJ[i * G:(i + 1) * G, L] = M + j * G + R[s]
            ADJ[M + j * G:M + (j + 1) * G, L] = i * G + R[inv[s]]
    total = 2 * M
    c = 0
    for src in [i * G for i in range(k)] + [M + j * G for j in range(k)]:
        c += _unreached(ADJ, total, src, D)
    return c


def _random_state(k, d, G, rng):
    P, V = [], []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        P.append(perm)
        V.append([rng.randrange(G) for _ in range(k)])
    return P, V


def _mutate(P, V, G, k, rng):
    P2 = [list(x) for x in P]
    V2 = [list(x) for x in V]
    L = rng.randrange(len(P2))
    if k > 1 and rng.random() < 0.3:
        a, b = rng.sample(range(k), 2)
        P2[L][a], P2[L][b] = P2[L][b], P2[L][a]
    else:
        i = rng.randrange(k)
        V2[L][i] = rng.randrange(G)
    return P2, V2


def _anneal(R, inv, G, k, d, D, rng, deadline, iters):
    """Simulated annealing over voltages and layer permutations. Returns (P, V, cost); P is None on failure."""
    P, V = _random_state(k, d, G, rng)
    cost = _cost(R, inv, G, k, D, P, V)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        P2, V2 = _mutate(P, V, G, k, rng)
        c2 = _cost(R, inv, G, k, D, P2, V2)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            P, V, cost = P2, V2, c2
        T = max(0.2, T * 0.999)
    if cost == 0:
        return P, V, 0
    return None, None, cost


def _edges_from(R, G, k, P, V):
    M = k * G
    E = []
    for L in range(len(P)):
        for i in range(k):
            j = P[L][i]
            row = R[V[L][i]]
            for g in range(G):
                E.append((i * G + g, M + j * G + int(row[g])))
    return 2 * M, E


def _lift_search(d, D, deadline, rng, get_best, consider):
    """Repeatedly sample a group and voltage assignment just above the current best order."""
    while time.monotonic() < deadline:
        best_n = get_best()
        k = 1 if rng.random() < 0.6 else rng.choice((2, 3))
        target = best_n // (2 * k) + 1
        G = max(2, target + rng.randrange(0, 6 if k == 1 else 3))
        tables = _group_tables(G, rng)
        if tables is None:
            continue
        R, inv = tables
        P, V, _ = _anneal(R, inv, G, k, d, D, rng, deadline, 2500)
        if P is not None:
            n, E = _edges_from(R, G, k, P, V)
            consider(n, E)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, 0.85 * time_limit - 1.5)
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 5:
        _lift_search(d, D, deadline, rng, lambda: best_n, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
