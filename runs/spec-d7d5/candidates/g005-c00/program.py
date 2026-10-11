import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bounds and projective-plane base (diameter 3).
# ----------------------------------------------------------------------------

def _moore(d, D):
    """Upper bound on the order of a bipartite graph with max degree d and diameter D."""
    return 2 * sum((d - 1) ** i for i in range(D))


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q > 40:
            continue
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Number-theory helpers and group tables.
# Each table is (G, RT) with RT[s, g] = g * s (right multiplication), identity at 0.
# ----------------------------------------------------------------------------

def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def _primitive_root(p):
    phi = p - 1
    factors = []
    x = phi
    f = 2
    while f * f <= x:
        if x % f == 0:
            factors.append(f)
            while x % f == 0:
                x //= f
        f += 1
    if x > 1:
        factors.append(x)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in factors):
            return g
    return 1


def _affine_table(p, t):
    """Affine group {x -> a x + b over Z_p : a in H}, |H| = t, t | p-1. Order p*t."""
    g0 = _primitive_root(p)
    h = pow(g0, (p - 1) // t, p)
    H = [pow(h, j, p) for j in range(t)]
    pos = np.full(p, -1, dtype=np.int64)
    for i, v in enumerate(H):
        pos[v] = i
    G = p * t
    idx = np.arange(G, dtype=np.int64)
    Hv = np.array(H, dtype=np.int64)
    A = Hv[idx // p]
    B = idx % p
    RT = np.empty((G, G), dtype=np.int64)
    for s in range(G):
        a2 = H[s // p]
        b2 = s % p
        na = (A * a2) % p
        nb = (A * b2 + B) % p
        RT[s] = pos[na] * p + nb
    return G, RT


def _semidirect_table(m, k, r):
    """Z_m x|_r Z_k with (a1,b1)(a2,b2) = (a1 + r^{b1} a2, b1 + b2); element (a,b) coded a*k+b."""
    G = m * k
    idx = np.arange(G, dtype=np.int64)
    A = idx // k
    B = idx % k
    powr = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    PB = powr[B]
    RT = np.empty((G, G), dtype=np.int64)
    for s in range(G):
        c, dd = divmod(s, k)
        RT[s] = ((A + PB * c) % m) * k + (B + dd) % k
    return G, RT


def _group_options(G, rng):
    opts = []
    for t in range(1, G + 1):
        if G % t:
            continue
        p = G // t
        if p >= 3 and _is_prime(p) and (p - 1) % t == 0:
            opts.append(("aff", p, t))
    for k in range(1, min(G, 16) + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        opts.append(("semi", m, k, 1))
        if k > 1:
            rs = [r for r in range(2, m)
                  if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if rs:
                for r in rng.sample(rs, min(len(rs), 3)):
                    opts.append(("semi", m, k, r))
    return opts


def _table(opt):
    if opt[0] == "aff":
        return _affine_table(opt[1], opt[2])
    _, m, k, r = opt
    return _semidirect_table(m, k, r)


# ----------------------------------------------------------------------------
# Two-orbit voltage lift search.
#
# Base graph: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}.
# For each base pair (i, j) there is a connection set S_ij in G; the lift has
# edges (A_i, x) -- (B_j, x*s) for s in S_ij and all x in G.
# Row sums and column sums of |S_ij| equal d, so the lift is d-regular and
# bipartite with 2*k*|G| vertices.
#
# Left multiplication is an automorphism, so the diameter test needs one BFS
# from each of the 2k base vertices (at the identity element).
# ----------------------------------------------------------------------------

def _cost(sets, RT, IR, G, k, D):
    """Total number of (source, vertex) pairs not reached within D steps."""
    total = 0
    sources = [(0, i) for i in range(k)] + [(1, j) for j in range(k)]
    for side0, b0 in sources:
        visA = np.zeros((k, G), dtype=bool)
        visB = np.zeros((k, G), dtype=bool)
        fA = [np.empty(0, dtype=np.int64) for _ in range(k)]
        fB = [np.empty(0, dtype=np.int64) for _ in range(k)]
        if side0 == 0:
            visA[b0, 0] = True
            fA[b0] = np.zeros(1, dtype=np.int64)
        else:
            visB[b0, 0] = True
            fB[b0] = np.zeros(1, dtype=np.int64)
        for _ in range(D):
            nA = np.zeros((k, G), dtype=bool)
            nB = np.zeros((k, G), dtype=bool)
            for i, j, S in sets:
                if fA[i].size:
                    # A_i element x reaches B_j element x*s.
                    nB[j, RT[S][:, fA[i]].ravel()] = True
                if fB[j].size:
                    # B_j element y reaches A_i element y*s^{-1}.
                    nA[i, IR[S][:, fB[j]].ravel()] = True
            nB &= ~visB
            nA &= ~visA
            if not nA.any() and not nB.any():
                break
            visA |= nA
            visB |= nB
            fA = [np.flatnonzero(nA[i]) for i in range(k)]
            fB = [np.flatnonzero(nB[j]) for j in range(k)]
        total += 2 * k * G - int(visA.sum()) - int(visB.sum())
    return total


def _anneal(pairs, RT, IR, G, k, D, rng, deadline, iters):
    """Anneal connection sets with the given sizes; return list of (i, j, S) with zero cost, or None."""
    sets = []
    for i, j, sz in pairs:
        sets.append([i, j, rng.sample(range(G), sz)])

    def evalc():
        return _cost([(i, j, np.array(S, dtype=np.int64)) for i, j, S in sets],
                     RT, IR, G, k, D)

    cost = evalc()
    T0, T1 = 2.0, 0.05
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        p = rng.randrange(len(sets))
        S = sets[p][2]
        pos = rng.randrange(len(S))
        x = rng.randrange(G)
        if x in S:
            continue
        old = S[pos]
        S[pos] = x
        c2 = evalc()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            S[pos] = old
    if cost == 0:
        return [(i, j, list(S)) for i, j, S in sets]
    return None


def _lift_edges(sets, RT, G, k):
    """Materialise the lift: A-blocks 0..k-1, B-blocks k..2k-1, each block of size G."""
    e = []
    for i, j, S in sets:
        for s in S:
            row = RT[s].tolist()
            for x in range(G):
                e.append((i * G + x, (k + j) * G + row[x]))
    return 2 * k * G, e


def _search(d, D, best, deadline, rng):
    bound = _moore(d, D)
    while time.monotonic() < deadline and best[0] < bound:
        k = 2 if rng.random() < 0.5 else 1
        lo = best[0] // (2 * k) + 1
        G = lo + rng.randrange(0, 12)
        if G < d:
            G = d
        opts = _group_options(G, rng)
        if not opts:
            continue
        opt = rng.choice(opts)
        G2, RT = _table(opt)
        if G2 < d:
            continue
        IR = np.argsort(RT, axis=1)
        if k == 1:
            pairs = [(0, 0, d)]
        else:
            a = rng.randrange(1, d)
            pairs = [(0, 0, a), (0, 1, d - a), (1, 0, d - a), (1, 1, a)]
        S = _anneal(pairs, RT, IR, G2, k, D, rng, deadline, 2500)
        if S is None:
            continue
        n, e = _lift_edges(S, RT, G2, k)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = (pg[0], pg[1])
        if d >= 3 and best[0] < _moore(d, D):
            best = _search(d, D, best, deadline, rng)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], best[1]
