import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe fallbacks: K_{d,d} (diameter 2) and PG(2,q) incidence (diameter 3).
# ----------------------------------------------------------------------------

def _fallback(d, D):
    """Best of K_{d,d} and the largest PG(2,q) incidence graph with q + 1 <= d (if D >= 3)."""
    best = lib.haar_graph(d, range(d))
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                break
    return best


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over a group G (order G) with ONE A-vertex and ONE B-vertex
# orbit. Vertices A_x = x and B_y = G + y. Connection set S (|S| = d, distinct):
#     A_x adjacent to B_{x*s} for s in S.
# Left multiplication by any element is an automorphism that is transitive on
# each side, so diameter <= D iff the eccentricity of A_e and of B_e is <= D.
# The graph is d-regular and bipartite by construction.
# ----------------------------------------------------------------------------

def _random_group(G, rng):
    """Return (m, k, r) with m*k = G describing a semidirect product Z_m x| Z_k, or None."""
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    rng.shuffle(divs)
    for k in divs[:24]:
        m = G // k
        if k == 1:
            return (m, 1, 1)
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if rs:
            return (m, k, rng.choice(rs))
    return None


def _unreached(G, tbl, S, Sinv, side, D):
    """Number of vertices NOT within distance D of the representative of `side` (0 = A, 1 = B)."""
    seen = bytearray(2 * G)
    src = side * G
    seen[src] = 1
    frontier = [src]
    count = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < G:
                row = tbl[u]
                for s in S:
                    v = G + row[s]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                row = tbl[u - G]
                for si in Sinv:
                    v = row[si]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        count += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return 2 * G - count


def _cost(G, tbl, invs, S, D):
    """Zero iff the lift of S has diameter <= D."""
    Sinv = [invs[s] for s in S]
    return _unreached(G, tbl, S, Sinv, 0, D) + _unreached(G, tbl, S, Sinv, 1, D)


def _climb(d, D, G, tbl, invs, rng, deadline, max_evals):
    """Hill-climb a connection set S of size d until cost 0 (plateau moves allowed)."""
    S = rng.sample(range(G), d)
    c = _cost(G, tbl, invs, S, D)
    evals = 0
    while c > 0 and evals < max_evals and time.monotonic() < deadline:
        i = rng.randrange(d)
        t = rng.randrange(G)
        if t in S:
            continue
        T = S[:]
        T[i] = t
        evals += 1
        ct = _cost(G, tbl, invs, T, D)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _bicayley_search(d, D, best, rng, deadline):
    """Repeatedly sample groups just above the current record half-order and climb to a valid S."""
    cache = {}
    while time.monotonic() < deadline:
        lo = max(d + 1, best[0] // 2 + 1)
        G = rng.randint(lo, lo + 30)
        spec = _random_group(G, rng)
        if spec is None:
            continue
        if spec in cache:
            tbl, invs = cache[spec]
        else:
            m, k, r = spec
            try:
                order, mul, inv = lib.semidirect_group(m, k, r)
            except ValueError:
                continue
            tbl = [[mul(x, y) for y in range(order)] for x in range(order)]
            invs = [inv(x) for x in range(order)]
            cache[spec] = (tbl, invs)
        S = _climb(d, D, G, tbl, invs, rng, deadline, 2000)
        if S is None:
            continue
        n = 2 * G
        edges = [(x, G + tbl[x][s]) for x in range(G) for s in S]
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _fallback(d, D)

    # Already at the Moore bound (e.g. the calibration case): nothing to gain.
    if d >= 3 and D >= 3 and best[0] < lib.moore_bound(d, D):
        rng = random.Random(seed)
        best = _bicayley_search(d, D, best, rng, deadline)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
