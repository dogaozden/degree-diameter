import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: K_{d,d}, projective-plane incidence, Araujo-Pardo-Lopez.
# ----------------------------------------------------------------------------

def _kdd(d):
    """K_{d,d}: diameter 2, valid for every D >= 2."""
    return lib.haar_graph(d, range(d))


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            try:
                return lib.projective_plane_incidence(q)
            except Exception:
                return None
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Bold change: bipartite Cayley graphs over non-abelian groups.
#
# Group G of order N (semidirect product Z_m x| Z_k). Connection set S, |S| = d.
# A_g is adjacent to B_{g s} for s in S. Left multiplication is an automorphism,
# so the diameter condition reduces to BFS from A_e and from B_e.
# This is a different search space from base-graph voltage lifts: the whole
# graph is one Cayley object and every group of the right order is a candidate.
# ----------------------------------------------------------------------------

def _group_candidates(G):
    """All semidirect-product presentations (m, k, r) with m * k = G."""
    out = []
    for k in range(1, 13):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _mul_table(order, mul):
    """Full multiplication table T[x][y] = x * y; identity is element 0."""
    return [[mul(x, y) for y in range(order)] for x in range(order)]


def _cost(G, T, S, Sinv, D):
    """Number of vertices not within distance D of A_e or of B_e (zero means valid)."""
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    row = T[u]
                    for s in S:
                        v = G + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - G]
                    for t in Sinv:
                        v = row[t]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _climb(G, T, inv, d, D, rng, iters, deadline):
    """Hill-climb a connection set S of size d; return S with zero cost, or None."""
    if d > G:
        return None
    S = rng.sample(range(G), d)
    Sinv = [inv[s] for s in S]
    c = _cost(G, T, S, Sinv, D)
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        x = rng.randrange(G)
        if x in S:
            continue
        i = rng.randrange(d)
        S2 = S[:]
        S2[i] = x
        Sinv2 = Sinv[:]
        Sinv2[i] = inv[x]
        c2 = _cost(G, T, S2, Sinv2, D)
        if c2 <= c:
            S, Sinv, c = S2, Sinv2, c2
    return S if c == 0 else None


def _cayley_graph(G, T, S):
    """Bipartite Cayley graph: A_g = g, B_h = G + h, edges A_g -- B_{g s}."""
    E = []
    for g in range(G):
        row = T[g]
        for s in S:
            E.append((g, G + row[s]))
    return 2 * G, E


def _search_order(G, d, D, rng, deadline):
    """Try groups of order G (random order) with several climbs each; return (n, edges) or None."""
    cands = _group_candidates(G)
    if not cands:
        return None
    rng.shuffle(cands)
    for (m, k, r) in cands:
        if time.monotonic() > deadline:
            break
        try:
            order, mul, _ = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        T = _mul_table(order, mul)
        inv = [row.index(0) for row in T]
        for _ in range(3):
            if time.monotonic() > deadline:
                break
            S = _climb(order, T, inv, d, D, rng, 400, deadline)
            if S is not None:
                return _cayley_graph(order, T, S)
    return None


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

    best = _kdd(d)
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Cayley-bigraph growth: try to beat the current order by searching
    # group orders G just above the best found so far (n = 2G).
    if d >= 2 and D >= 2:
        G_best = best_n // 2
        frac = 8
        while time.monotonic() < deadline:
            inc = max(1, G_best // frac)
            G = G_best + inc
            attempt = min(deadline, time.monotonic() + 4.0)
            res = _search_order(G, d, D, rng, attempt)
            if res is not None and consider(res[0], res[1]):
                G_best = res[0] // 2
                frac = 8
            else:
                frac = min(frac * 2, 4 * (G_best + 1))

    if not lib.is_valid(best[0], best[1], d, D):
        best = _kdd(d)
    return best
