import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over finite groups G (order N), searched by annealing.
#
# Vertices A_x = x and B_y = G + y. Connection set S = {s_1..s_d}, all distinct.
# Edge A_x ~ B_{x*s} for every x in G and s in S. Each vertex has degree d, and
# the graph is bipartite. Left multiplication is an automorphism, so the
# diameter is at most D iff BFS from A_1 and from B_1 reaches all 2G vertices
# within D steps. The cost is the number of unreached vertices from those two
# sources, and cost 0 means a valid graph.
#
# This is a different family from the voltage lifts in the parent: a single
# layer over one group, with the group chosen as cyclic or metacyclic
# Z_m x| Z_k, and searched in order of ascending order G so that the first
# valid hit beats the current record.
# ----------------------------------------------------------------------------


def _cost(adj, G, D):
    """Unreached (source, vertex) pairs from A_1 (node 0) and B_1 (node G) within D steps."""
    N = adj.shape[0]
    total = 0
    for src in (0, G):
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = adj[front].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            front = nb
        total += N - int(np.count_nonzero(seen))
    return total


def _adj(M, inv, S):
    """Adjacency array of shape (2G, d): A-rows list B-nodes, B-rows list A-nodes."""
    G = M.shape[0]
    Sa = np.asarray(S, dtype=np.int64)
    return np.vstack([G + M[:, Sa], M[:, inv[Sa]]])


def _group(spec):
    """Multiplication table M and inverse array inv for the group given by spec."""
    m, k, r = spec
    order, mul, inv_f = lib.semidirect_group(m, k, r)
    M = np.empty((order, order), dtype=np.int64)
    for x in range(order):
        M[x, :] = [mul(x, y) for y in range(order)]
    inv = np.array([inv_f(x) for x in range(order)], dtype=np.int64)
    ar = np.arange(order)
    if not (np.array_equal(M[0], ar) and np.array_equal(M[:, 0], ar)):
        raise ValueError("identity check failed")
    return order, M, inv


def _specs(G, rng, cap=4):
    """Group specs (m, k, r) of order G: cyclic, and Z_m x| Z_k for several divisors k."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            out.append((m, 1, 1))
            continue
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(cands)
        out.extend((m, k, r) for r in cands[:cap])
    rng.shuffle(out)
    return out


def _anneal(M, inv, G, d, D, rng, deadline, iters=1500):
    """Annealed search over connection sets S of size d. Returns S with cost 0, or None."""
    while time.monotonic() < deadline:
        S = rng.sample(range(G), d)
        c = _cost(_adj(M, inv, S), G, D)
        T = 2.0
        for _ in range(iters):
            if c == 0:
                return S
            if time.monotonic() >= deadline:
                return None
            i = rng.randrange(d)
            x = rng.randrange(G)
            if x in S:
                continue
            T2 = S[:]
            T2[i] = x
            c2 = _cost(_adj(M, inv, T2), G, D)
            if c2 <= c or rng.random() < math.exp((c - c2) / T):
                S, c = T2, c2
            T = max(0.1, T * 0.998)
        if c == 0:
            return S
    return None


def _edges(M, S, G):
    """Edge list of the bi-Cayley graph (2G vertices). Distinct s give distinct neighbours."""
    return 2 * G, [(x, G + int(M[x, s])) for x in range(G) for s in S]


def _search(d, D, lo, hi, deadline, rng):
    """Yield (n, edges) for each bi-Cayley graph found, with orders G increasing."""
    floor_G = lo - 1
    rnd = 0
    while time.monotonic() < deadline:
        budget = min(8.0, 0.7 * (1.7 ** rnd))
        rnd += 1
        for G in range(lo, hi + 1):
            if time.monotonic() >= deadline:
                return
            if G <= floor_G:
                continue
            for spec in _specs(G, rng)[:2]:
                if time.monotonic() >= deadline:
                    return
                try:
                    order, M, inv = _group(spec)
                except Exception:
                    continue
                if order != G:
                    continue
                sub = min(deadline, time.monotonic() + budget)
                S = _anneal(M, inv, G, d, D, rng, sub)
                if S is not None:
                    floor_G = G
                    yield _edges(M, S, G)
                    break


# ----------------------------------------------------------------------------
# Build.
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
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
            return True
        return False

    # Projective plane incidence graph: diameter 3 and optimal when d-1 is a prime power.
    if D >= 3 and 2 <= d - 1 <= 40 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)

    # Bi-Cayley search over groups of order G, giving 2G vertices.
    # Only orders G with 2G above the current best are tried.
    moore = lib.moore_bound(d, D)
    if D >= 3 and d >= 3 and best_n < moore:
        lo = max(best_n // 2 + 1, int(0.4 * moore / 2), 2 * d)
        hi = lo + 24
        for n, e in _search(d, D, lo, hi, deadline, rng):
            consider(n, e)
            if time.monotonic() >= deadline:
                break

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
