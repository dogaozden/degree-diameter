import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley (Haar-type) graphs over semidirect products Z_m x| Z_k.
#
# Vertices: A_g = g and B_h = G + h for g, h in the group of order G.
# Edges: A_g ~ B_{g*s} for s in a connection set S with |S| = d.
# Every edge joins A to B, so the graph is bipartite and d-regular.
#
# Left multiplication is an automorphism, so the diameter is <= D iff the
# balls of radius D around A_e and B_e cover the whole graph. That makes each
# evaluation two BFS passes, which is much cheaper than checking all sources.
# The search hill-climbs over S for many group orders just above the current
# record, and keeps only graphs that pass lib.is_valid.
# ----------------------------------------------------------------------------


def _kdd(d):
    """K_{d,d}: diameter 2, valid for every D >= 2."""
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


def _groups(G):
    """All semidirect products Z_m x| Z_k of order G as (m, k, r) with r^k = 1 mod m, gcd(r, m) = 1."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        for r in range(1, m + 1):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r, G):
    """Multiplication table (as lists) and inverse list for Z_m x| Z_k, element (a, b) coded as a*k+b."""
    idx = np.arange(G, dtype=np.int64)
    a = idx // k
    b = idx % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    # (a, b)*(c, e) = (a + r^b c, b + e)
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    inv = np.argmax(M == 0, axis=1)
    return M.tolist(), inv.tolist()


def _cost(S, M, inv, G, D):
    """Number of ordered (source, target) pairs not reached within D, from A_e and from B_e."""
    Si = [inv[s] for s in S]
    tot = 0
    N2 = 2 * G
    for src in (0, G):
        seen = bytearray(N2)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    row = M[u]
                    for s in S:
                        v = row[s] + G
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = M[u - G]
                    for si in Si:
                        v = row[si]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        tot += N2 - cnt
    return tot


def _search(G, d, D, M, inv, rng, deadline, iters):
    """Hill-climb a connection set S of size d; return (S or None, final cost)."""
    S = rng.sample(range(G), d)
    c = _cost(S, M, inv, G, D)
    for _ in range(iters):
        if c == 0:
            return S, 0
        if time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        ct = _cost(T, M, inv, G, D)
        if ct <= c or rng.random() < 0.03:
            S, c = T, ct
    return (S if c == 0 else None), c


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_candidate(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    # Stop well before the limit; the final validity check is cheap.
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _kdd(d)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo_candidate(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Bi-Cayley search: order G must satisfy 2G > current best, and G >= d.
    lo = max(d, best[0] // 2 + 1)
    while time.monotonic() < deadline:
        G = rng.randint(lo, lo + max(2, lo // 40))
        groups = _groups(G)
        for _ in range(2):
            if time.monotonic() >= deadline:
                break
            m, k, r = rng.choice(groups)
            M, inv = _tables(m, k, r, G)
            S, _c = _search(G, d, D, M, inv, rng, deadline, 1200)
            if S is not None:
                n = 2 * G
                e = [(g, G + M[g][s]) for g in range(G) for s in S]
                consider(n, e)
                break
        lo = max(d, best[0] // 2 + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = _kdd(d)
    return best
