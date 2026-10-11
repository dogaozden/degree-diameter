import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Baseline families: projective plane incidence (D >= 3) and Araujo-Pardo-Lopez
# (D = 3). The safe fallback is K_{d,d}.
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_candidate(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New construction: bi-Cayley graphs over many small groups of a chosen order.
#
# Vertices A_x = x and B_y = G + y for x, y in G. Connection set S (|S| = d,
# distinct group elements). Edge A_x ~ B_{x*s} for every x and s in S.
# The graph is d-regular and bipartite. Left multiplication is an automorphism,
# so diameter <= D iff the vertices reached from A_1 and B_1 within D steps
# cover everything. The cost counts unreached vertices from those two sources.
#
# Groups are semidirect products Z_m x| Z_k with element (a, b) coded as a*k+b,
# multiplication (a, b)(c, d) = (a + r^b c, b + d), r^k = 1 mod m. The table is
# built vectorised. Every candidate is still checked with lib.is_valid.
#
# Differences from the previous approach: orders are sampled over a window of
# candidate orders that can beat the record (2G > 684 needs G >= 343), with
# many non-cyclic groups per order (direct products, twisted products), and
# each (group, order) gets a short annealing run over connection sets.
# ----------------------------------------------------------------------------

def _divisor_specs(G, rng, per_pair=6):
    """Group specs (m, k, r) with m*k = G: cyclic, direct and twisted products."""
    specs = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            specs.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:per_pair]:
            specs.append((m, k, r))
    return specs


def _group_table(m, k, r):
    """Multiplication table M[x, y] = x*y for Z_m x| Z_k (element (a, b) coded as a*k + b)."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    part = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    return part * k + (b[:, None] + b[None, :]) % k


def _cost(M, inv, G, S, D):
    """Unreached (source, vertex) pairs from A_0 and B_0 within D steps. Zero means valid."""
    Sa = np.asarray(S, dtype=np.int64)
    adj = np.vstack([G + M[:, Sa], M[:, inv[Sa]]])
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = adj[frontier].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            frontier = nb
        total += N - int(np.count_nonzero(seen))
    return total


def _anneal(M, inv, G, d, D, deadline, rng, iters):
    """Annealed search over connection sets S of size d. Returns (S or None, cost)."""
    S = rng.sample(range(G), d)
    c = _cost(M, inv, G, S, D)
    T = 1.5
    for _ in range(iters):
        if c == 0 or time.monotonic() >= deadline:
            break
        T = max(0.08, T * 0.998)
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        S2 = list(S)
        S2[i] = x
        c2 = _cost(M, inv, G, S2, D)
        if c2 <= c or rng.random() < math.exp((c - c2) / T):
            S, c = S2, c2
    return (S if c == 0 else None), c


def _bc_edges(M, G, S):
    """Edge list of the bi-Cayley graph: A_x = x joined to B_y = G + (x*s)."""
    E = [(x, G + int(M[x, s])) for x in range(G) for s in S]
    return 2 * G, E


def _bicayley_search(d, D, best_n, lo, hi, deadline, rng, consider):
    """Repeatedly pick an order in the window that can beat best_n, a group, and anneal S."""
    while time.monotonic() < deadline:
        floor = max(lo, best_n // 2 + 1)
        top = max(hi, floor + 10)
        G = rng.randint(floor, top)
        specs = _divisor_specs(G, rng)
        if not specs:
            continue
        m, k, r = rng.choice(specs)
        try:
            M = _group_table(m, k, r)
        except Exception:
            continue
        ar = np.arange(G)
        if not (np.array_equal(M[0], ar) and np.array_equal(M[:, 0], ar)):
            continue
        inv = np.argmax(M == 0, axis=1)
        sub = min(deadline, time.monotonic() + 3.0)
        S, _ = _anneal(M, inv, G, d, D, sub, rng, 8000)
        if S is not None:
            n, E = _bc_edges(M, G, S)
            consider(n, E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.82 * time_limit
    rng = random.Random(seed * 1000003 + d * 131 + D)

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

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo_candidate(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 4 and d >= 3:
        moore_half = lib.moore_bound(d, D) // 2
        lo = max(2 * d, int(0.42 * moore_half))
        hi = lo + max(40, lo // 5)
        _bicayley_search(d, D, best_n, lo, hi, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
