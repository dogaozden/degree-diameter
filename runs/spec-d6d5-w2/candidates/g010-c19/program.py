import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Projective-plane baseline (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: bi-Cayley graphs certified by set covering.
#
# For a finite group G with multiplication M[x][y] (identity 0) and a connection
# set S of d distinct elements, the bipartite graph has vertices A_x, B_y (x, y in G)
# with A_x ~ B_{x s} for s in S. The graph is vertex-transitive on each side, so the
# diameter condition reduces to three set-coverage tests on the group:
#
#   T  = { s t^-1 : s, t in S }        (A-to-A steps of length 2)
#   T' = { s^-1 t : s, t in S }        (B-to-B steps of length 2)
#   A-A and B-B even distances <= D:  T^{<=a} = G  and  T'^{<=a} = G,  a = floor(D/2)
#   A-B odd distances <= D:           T^{<=b} S = G,                    b = floor((D-1)/2)
#
# Evaluating these costs about a thousand set operations, far cheaper than a BFS
# over the whole lift, so simulated annealing over S can run thousands of
# candidates per second. Groups are semidirect products Z_m x| Z_k of order G.
# ----------------------------------------------------------------------------

def _ball(gen, r, M):
    """Set of products of at most r elements of gen (gen contains the identity)."""
    X = {0}
    for _ in range(r):
        X = {M[x][t] for x in X for t in gen}
    return X


def _cover_cost(S, M, inv, G, a, b):
    """Total number of group elements left uncovered by the three coverage tests. Zero means valid."""
    T = {M[s][inv[t]] for s in S for t in S}
    Tp = {M[inv[s]][t] for s in S for t in S}
    XA = _ball(T, a, M)
    XC = XA if b == a else _ball(T, b, M)
    Y = {M[x][s] for x in XC for s in S}
    XB = _ball(Tp, a, M)
    return (G - len(XA)) + (G - len(Y)) + (G - len(XB))


def _tables(m, k, r):
    """Multiplication and inverse tables of Z_m x|_r Z_k, element (a, b) coded as a*k + b."""
    G = m * k
    idx = np.arange(G, dtype=np.int64)
    A = idx // k
    B = idx % k
    P = np.array([pow(r, bb, m) for bb in range(k)], dtype=np.int64)
    M = ((A[:, None] + P[B][:, None] * A[None, :]) % m) * k + (B[:, None] + B[None, :]) % k
    rows, cols = np.nonzero(M == 0)
    inv = np.empty(G, dtype=np.int64)
    inv[rows] = cols
    return M.tolist(), inv.tolist()


def _groups_of_order(G, rng):
    """Cyclic group plus sampled semidirect products Z_m x| Z_k of order G, shuffled."""
    out = [(G, 1, 1)]
    for k in range(2, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        if len(rs) > 4:
            rs = rng.sample(rs, 4)
        out.extend((m, k, r) for r in rs)
    rng.shuffle(out)
    return out


def _anneal_S(M, inv, G, d, a, b, rng, deadline):
    """Simulated annealing over connection sets S of size d; returns a zero-cost S or None."""
    S = rng.sample(range(G), d)
    c = _cover_cost(S, M, inv, G, a, b)
    temp = 2.0
    while c > 0 and time.monotonic() < deadline:
        temp = max(0.15, temp * 0.9995)
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _cover_cost(S2, M, inv, G, a, b)
        if c2 <= c or rng.random() < math.exp((c - c2) / temp):
            S, c = S2, c2
    return S if c == 0 else None


def _bicayley_edges(G, M, S):
    """Edges of the bi-Cayley graph: A_x = x, B_y = G + y, A_x ~ B_{x s}."""
    E = [(x, G + M[x][s]) for x in range(G) for s in S]
    return 2 * G, E


def _try_order(G, d, a, b, rng, end, budget, consider):
    """Try several groups of order G with annealing; True if a valid graph of order 2G was accepted."""
    groups = _groups_of_order(G, rng)
    t_end = min(end, time.monotonic() + budget)
    per = max(0.4, budget / 3.0)
    for m, k, r in groups:
        now = time.monotonic()
        if now >= t_end:
            break
        M, inv = _tables(m, k, r)
        S = _anneal_S(M, inv, G, d, a, b, rng, min(t_end, now + per))
        if S is not None:
            n, e = _bicayley_edges(G, M, S)
            if consider(n, e):
                return True
    return False


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + max(1.0, 0.85 * time_limit - 1.5)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = 2 * d, lib.haar_graph(d, range(d))[1]

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
            return True
        return False

    if d == 2 and D >= 2:
        # Cycle of length 2D has diameter D.
        consider(*lib.haar_graph(D, [0, 1]))
        return best_n, best_e

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(*pg)
        return best_n, best_e

    if D >= 4 and d >= 3:
        a, b = D // 2, (D - 1) // 2
        lo = max(best_n // 2, d + 1)   # largest group order known to work
        step = 8
        while time.monotonic() < end:
            G = lo + step
            budget = 3.0 if step > 1 else 5.0
            ok = _try_order(G, d, a, b, rng, end, budget, consider)
            if ok:
                lo = G
                step = min(step * 2, 64)
            else:
                step = max(1, step // 2)

    if not lib.is_valid(best_n, best_e, d, D):
        return 2 * d, lib.haar_graph(d, range(d))[1]
    return best_n, best_e
