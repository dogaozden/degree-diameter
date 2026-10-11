import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families: projective plane incidence graph (D >= 3) and the
# Araujo-Pardo-Lopez graph. Their orders are kept as the floor to beat.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New helper: bi-Cayley graphs over finite groups, searched with a two-root cost.
#
# Vertices: A_g = g and B_h = G + h for g, h in the group G (identity = 0).
# Edges:    A_g -- B_{g*s} for every s in a connection set S with |S| = d.
#
# Left multiplication by x maps A_g -> A_{xg} and B_h -> B_{xh} and preserves
# the edge set, so the automorphism group is transitive on each side. Hence
#   diameter <= D  <=>  BFS from A_e and from B_e both reach all 2|G| vertices
#                        within D steps.
# Only two BFS runs per candidate are needed, instead of one per vertex.
# Left-multiplication invariance also gives a bipartite, d-regular graph
# automatically, since S has distinct elements.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k of order G, returned as (order, mul, inv), or None."""
    divs = [k for k in range(1, G + 1) if G % k == 0]
    for _ in range(40):
        k = rng.choice(divs)
        m = G // k
        if k == 1 or m == 1:
            r = 1
        else:
            cands = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, inv = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        return order, mul, inv
    return None


def _tables(G, mul, inv):
    """Full multiplication table M[x][y] and inverse list for a group of order G."""
    M = [[mul(x, y) for y in range(G)] for x in range(G)]
    iv = [inv(x) for x in range(G)]
    return M, iv


def _cost(G, M, S, invS, D, limit):
    """Unreached (root, vertex) pairs over the two roots A_e and B_e within distance D.

    Zero means the bi-Cayley graph of S has diameter <= D. Returns early once the
    running total exceeds `limit`.
    """
    N = 2 * G
    total = 0
    for root in (0, G):
        seen = bytearray(N)
        seen[root] = 1
        frontier = [root]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    row = M[u]
                    for s in S:
                        v = G + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = M[u - G]
                    for si in invS:
                        v = row[si]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
        if total > limit:
            return total
    return total


def _anneal_S(d, D, G, M, iv, rng, deadline, max_iter):
    """Simulated annealing over connection sets S (size d) in the group of order G.

    Returns (S, cost) with S None unless cost == 0.
    """
    S = rng.sample(range(G), d)
    invS = [iv[s] for s in S]
    inf = float("inf")
    c = _cost(G, M, S, invS, D, inf)
    T = 1.0
    for it in range(max_iter):
        if c == 0:
            break
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.999)
        limit = c - T * math.log(1.0 - rng.random())
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        S2 = S[:]
        S2[i] = new
        inv2 = invS[:]
        inv2[i] = iv[new]
        c2 = _cost(G, M, S2, inv2, D, limit)
        if c2 <= limit:
            S, invS, c = S2, inv2, c2
    return (S if c == 0 else None), c


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
    best_n = best[0]
    target = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # A graph already at the Moore bound cannot be beaten.
    if best_n >= target:
        return best

    # Ratchet search: find a bi-Cayley graph on a group of order G, then move to G + 1.
    # Each G tries random semidirect groups of that order, each for a short slice.
    Gcur = max(d, best_n // 2 + 1)
    Gmax = target // 2
    while time.monotonic() < deadline and Gcur <= Gmax:
        found = None
        misses = 0
        while time.monotonic() < deadline and found is None and misses < 150:
            g = _sample_group(Gcur, rng)
            if g is None:
                misses += 1
                continue
            order, mul, inv = g
            M, iv = _tables(order, mul, inv)
            slice_end = min(deadline, time.monotonic() + 1.5)
            S, _ = _anneal_S(d, D, order, M, iv, rng, slice_end, 200000)
            if S is not None:
                found = (order, M, S)
        if found is None:
            if misses >= 150:
                Gcur += 1
                continue
            break
        order, M, S = found
        E = [(g, order + M[g][s]) for g in range(order) for s in S]
        consider(2 * order, E)
        if best_n >= target:
            break
        Gcur = order + 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
