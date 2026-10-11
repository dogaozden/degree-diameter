import math
import random
import time
from math import gcd

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Construction used for the large D >= 3 cases: a d-regular bi-Cayley graph
# over a finite group G with 2|G| vertices (one "A" and one "B" orbit).
#
# Vertices A_g and B_h (g, h in G). Edges A_g -- B_{g*s} for s in a connection
# set S of d distinct group elements. Left multiplication is an automorphism,
# so the diameter check reduces to two breadth-first searches of depth D, one
# rooted at A_e and one at B_e, using vectorised numpy frontiers over the
# group multiplication table. This is a search over connection sets for many
# groups (semidirect products Z_m x| Z_k and direct products), with simulated
# annealing on the number of unreached vertices, rather than a voltage lift
# over a few base vertices.
# ----------------------------------------------------------------------------


def _group_table(m, k, r):
    """Multiplication table and inverse array of Z_m x|_r Z_k (element (a, b) coded a*k + b)."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    P = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    # (a, b) * (c, e) = (a + r^b c, b + e)
    MT = ((a[:, None] + P[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    rows, cols = np.nonzero(MT == 0)
    if len(rows) != G or not np.array_equal(rows, np.arange(G)):
        return None
    inv = np.empty(G, dtype=np.int64)
    inv[rows] = cols
    return MT, inv


def _group_options(G):
    """(m, k, r) triples with m * k = G giving a group Z_m x|_r Z_k."""
    opts = []
    for k in range(1, min(G, 16) + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _bfs_uncovered(cols, rcols, G, D, root_is_a):
    """Number of vertices not within distance D of the root (A_e or B_e)."""
    visA = np.zeros(G, dtype=bool)
    visB = np.zeros(G, dtype=bool)
    if root_is_a:
        visA[0] = True
        front = visA.copy()
        from_a = True
    else:
        visB[0] = True
        front = visB.copy()
        from_a = False
    for _ in range(D):
        if not front.any():
            break
        idx = np.flatnonzero(front)
        nxt = np.zeros(G, dtype=bool)
        if from_a:
            nxt[cols[idx].ravel()] = True
            nxt &= ~visB
            visB |= nxt
        else:
            nxt[rcols[idx].ravel()] = True
            nxt &= ~visA
            visA |= nxt
        front = nxt
        from_a = not from_a
    return 2 * G - int(visA.sum()) - int(visB.sum())


def _cost(MT, inv, S, G, D):
    """Zero iff the bi-Cayley graph with connection set S has diameter <= D."""
    idx = np.array(S, dtype=np.int64)
    cols = MT[:, idx]          # A_g -> B_{g s}
    rcols = MT[:, inv[idx]]    # B_h -> A_{h s^-1}
    return _bfs_uncovered(cols, rcols, G, D, True) + _bfs_uncovered(cols, rcols, G, D, False)


def _anneal(MT, inv, G, d, D, rng, t_end):
    """Anneal a connection set S of size d; returns S with zero cost, or None at t_end."""
    S = rng.sample(range(G), d)
    cost = _cost(MT, inv, S, G, D)
    T = 1.5
    while cost > 0:
        if time.monotonic() >= t_end:
            return None
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        S2 = S[:]
        S2[i] = new
        c2 = _cost(MT, inv, S2, G, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            S, cost = S2, c2
        T = max(0.2, T * 0.999)
    return S


def _edges_from(MT, S, G):
    E = []
    for s in S:
        col = MT[:, s].tolist()
        E.extend((g, G + h) for g, h in enumerate(col))
    return E


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 4.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle C_{2D}: order 2D is the Moore bound for d = 2.
        edges = []
        for i in range(D):
            edges.append((i, D + i))
            edges.append((i, D + (i + 1) % D))
        return 2 * D, edges

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = [best_n, best_e]

    def consider(n, e):
        nonlocal best_n
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e
            best_n = n
            return True
        return False

    if D == 2:
        return best[0], best[1]

    # Cheap algebraic records for D >= 3.
    try:
        if lib.is_prime_power(d - 1):
            n_pg, e_pg = lib.projective_plane_incidence(d - 1)
            consider(n_pg, e_pg)
    except Exception:
        pass
    try:
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            n_ar, e_ar = lib.araujo_lopez_graph(q)
            consider(n_ar, e_ar)
    except Exception:
        pass

    moore = lib.moore_bound(d, D)
    rng = random.Random(seed)
    opt_cache = {}
    slice_len = 2.5

    try:
        lo = best[0] // 2 + 1
        while time.monotonic() < deadline and 2 * lo <= moore:
            G = lo + rng.choice([0, 0, 0, 1, 1, 2, 3, 5])
            if 2 * G > moore:
                G = lo
            if G not in opt_cache:
                opt_cache[G] = _group_options(G)
            opts = opt_cache[G]
            if not opts:
                continue
            m, k, r = rng.choice(opts)
            tab = _group_table(m, k, r)
            if tab is None:
                continue
            MT, inv = tab
            t_end = min(deadline, time.monotonic() + slice_len)
            S = _anneal(MT, inv, G, d, D, rng, t_end)
            if S is not None:
                consider(2 * G, _edges_from(MT, S, G))
            lo = max(lo, best[0] // 2 + 1)
    except Exception:
        pass

    n_out, e_out = best[0], best[1]
    if not lib.is_valid(n_out, e_out, d, D):
        return lib.haar_graph(d, range(d))
    return n_out, e_out
