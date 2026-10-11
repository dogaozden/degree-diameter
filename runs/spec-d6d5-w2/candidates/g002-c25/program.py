import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Haar-type bi-Cayley graphs over groups of order G (Z_m and semidirect
# products Z_m x| Z_k). Vertices a_x = x and b_y = G + y. Each s in S gives
# edges a_x ~ b_{x*s}. For d = 6, D = 5 this is a different search space from
# the voltage lifts used before: one group, one connection set of size d, and
# a plain annealer over the set S.
#
# Diameter check: G acts on both sides by left multiplication and preserves
# edges, so the graph has diameter <= D iff a_0 and b_0 both reach every
# vertex within D steps. Only two BFS runs are needed per evaluation.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul, inv) for a random group of order G (cyclic or semidirect)."""
    for _ in range(40):
        k = rng.choice([2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k:
            continue
        m = G // k
        if m < 3:
            continue
        cands = [r for r in rng.sample(range(2, m), min(m - 2, 80))
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not cands:
            continue
        try:
            return lib.semidirect_group(m, k, rng.choice(cands))
        except ValueError:
            continue
    return lib.cyclic_group(G)


def _haar_cost(S, G, D, cols):
    """Unreached (vertex, source) pairs from a_0 and b_0 within distance D. Zero means diameter <= D."""
    F = [cols(s)[0] for s in S]
    B = [cols(s)[1] for s in S]
    total = 0
    for src in (0, G):
        seen = bytearray(2 * G)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    for f in F:
                        v = G + f[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    y = u - G
                    for b in B:
                        v = b[y]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * G - cnt
    return total


def _anneal_haar(G, d, D, mul, inv, rng, deadline, iters):
    """Anneal a connection set S of size d containing the identity (0). Returns S or None."""
    fwd_cache, bwd_cache = {}, {}

    def cols(s):
        if s not in fwd_cache:
            fwd_cache[s] = [mul(x, s) for x in range(G)]
            si = inv(s)
            bwd_cache[s] = [mul(y, si) for y in range(G)]
        return fwd_cache[s], bwd_cache[s]

    S = [0] + rng.sample(range(1, G), d - 1)
    c = _haar_cost(S, G, D, cols)
    T = 0.6
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        t = rng.randrange(1, G)
        if t in S:
            continue
        S2 = S[:]
        S2[i] = t
        c2 = _haar_cost(S2, G, D, cols)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = S2, c2
        T = max(0.05, T * 0.999)
    return S if c == 0 else None


def _haar_edges(G, S, mul):
    """Edges of the bi-Cayley graph: a_x = x, b_y = G + y, a_x ~ b_{x*s}."""
    return [(x, G + mul(x, s)) for x in range(G) for s in S]


# ----------------------------------------------------------------------------
# Small-case constructions.
# ----------------------------------------------------------------------------

def _complete_bip(d):
    """K_{d,d}: 2d vertices, diameter 2."""
    return lib.haar_graph(d, range(d))


def _cycle(D):
    """Even cycle C_{2D}: bipartite, degree 2, diameter D."""
    n = 2 * D
    return n, [(i, (i + 1) % n) for i in range(n)]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n, e = _cycle(D)
        return (n, e) if lib.is_valid(n, e, d, D) else _complete_bip(d)

    best_n, best_e = _complete_bip(d)
    if D == 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # D = 3 shortcuts: projective plane incidence and Araujo-Pardo-Lopez.
    if D == 3:
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Main search: Haar-type bi-Cayley graphs over varying groups.
    # Each success raises the target order; failures try other groups and sizes.
    rng = random.Random(seed * 1000003 + d * 97 + D)
    moore = lib.moore_bound(d, D)
    m_lo = max(d + 1, (moore // 2) * 3 // 10)
    while time.monotonic() < deadline:
        m_lo = max(m_lo, best_n // 2 + 1, d + 1)
        spread = max(3, m_lo // 25)
        G = rng.randint(m_lo, m_lo + spread)
        order, mul, inv = _sample_group(G, rng)
        S = _anneal_haar(order, d, D, mul, inv, rng, deadline, 2000)
        if S is not None:
            consider(2 * order, _haar_edges(order, S, mul))

    if not lib.is_valid(best_n, best_e, d, D):
        return _complete_bip(d)
    return best_n, best_e
