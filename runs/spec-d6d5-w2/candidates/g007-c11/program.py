import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bipartite Cayley-type search (bi-Cayley over k = 1, i.e. a bipartite double
# of a Cayley graph) on semidirect products Z_m x| Z_k.
#
# Vertices: L_g = g and R_h = G + h, for g, h in the group of order G.
# Edges:    L_g -- R_{g*s} for each s in the connection set S (|S| = d).
#
# Left multiplication by group elements is an automorphism that moves L_x to
# L_e and R_y to R_{x^-1 y}, so all pairwise distances are determined by BFS
# from L_e (covers L-L and L-R pairs) and from R_e (covers R-R and R-L pairs).
# Diameter <= D holds iff both BFS runs reach everything within D steps.
#
# Unlike the parent's multi-layer voltage annealing, this is a single-layer
# connection-set hill climb with far cheaper cost evaluation, so it can test
# many more groups and sets within the budget.
# ----------------------------------------------------------------------------

def _bad_pairs(S, G, mul, Sinv, D, limit):
    """Number of (source, vertex) pairs not reached within D steps from L_e and R_e.

    Zero iff the bipartite Cayley graph with connection set S has diameter <= D.
    Returns early once the running total exceeds `limit`.
    """
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
                    row = mul[u]
                    for s in S:
                        v = G + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = mul[u - G]
                    for si in Sinv:
                        v = row[si]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
        if total > limit:
            return total
    return total


def _climb(G, d, D, mul, invs, rng, deadline):
    """Hill-climb a connection set S (|S| = d) in the group until all pairs are within D.

    Returns S on success, None on timeout. Occasionally accepts a worse move
    to escape plateaus.
    """
    S = rng.sample(range(G), d)
    c = _bad_pairs(S, G, mul, [invs[s] for s in S], D, float("inf"))
    while c > 0:
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        Tinv = [invs[s] for s in T]
        if rng.random() < 0.02:
            ct = _bad_pairs(T, G, mul, Tinv, D, float("inf"))
            accept = True
        else:
            ct = _bad_pairs(T, G, mul, Tinv, D, c)
            accept = ct <= c
        if accept:
            S, c = T, ct
    return S


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k of order G as (mul_table, inverse_list), or None."""
    ks = [k for k in (1, 2, 3, 4, 6, 8, 9, 12) if G % k == 0 and G // k >= 2]
    if not ks:
        return None
    k = rng.choice(ks)
    m = G // k
    if k == 1:
        r = 1
    else:
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
    order, mul, inv = lib.semidirect_group(m, k, r)
    table = [[mul(x, y) for y in range(order)] for x in range(order)]
    invs = [inv(x) for x in range(order)]
    return table, invs


def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best_n = 2 * d
    best_e = [(i, d + j) for i in range(d) for j in range(d)]

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    deadline = start + min(0.85 * time_limit, time_limit - 3.0)
    span = max(0.0, deadline - start)
    if time.monotonic() >= deadline or best_n >= moore:
        return best_n, best_e

    rng = random.Random(seed * 1000003 + d * 101 + D)

    # Algebraic candidates (cheap, deterministic).
    q = d - 1
    if D >= 3 and q >= 2 and lib.is_prime_power(q):
        try:
            consider(*lib.projective_plane_incidence(q))
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Main search: bipartite Cayley graphs over varied semidirect products.
    per_attempt = max(0.5, 0.06 * span)
    while time.monotonic() < deadline and best_n < moore:
        best_G = best_n // 2
        moore_half = moore // 2
        lo = max(best_G + 1, moore_half // 4, d)
        if lo > moore_half:
            break
        hi = min(moore_half, lo + max(3, lo // 10))
        G = rng.randint(lo, hi)

        grp = _sample_group(G, rng)
        if grp is None:
            continue
        mul, invs = grp

        attempt_deadline = min(deadline, time.monotonic() + per_attempt)
        S = _climb(G, d, D, mul, invs, rng, attempt_deadline)
        if S is not None:
            n = 2 * G
            e = [(g, G + mul[g][s]) for g in range(G) for s in S]
            consider(n, e)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n = 2 * d
        best_e = [(i, d + j) for i in range(d) for j in range(d)]
    return best_n, best_e
