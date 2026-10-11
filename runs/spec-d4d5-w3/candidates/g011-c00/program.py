import math
import random
import time

import lib

# Share of time_limit used for searching; the rest is margin.
SEARCH_FRAC = 0.80
# Hill-climb steps per random start.
CLIMB_ITERS = 500


# ----------------------------------------------------------------------------
# Safe fallbacks and the Moore-optimal D = 3 case.
# ----------------------------------------------------------------------------

def _safe(d, D):
    """Always-valid small graph: K_{d,d} for D >= 2, with trivial cases handled first."""
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]
    return lib.haar_graph(d, range(d))


def _pg_case(d, D):
    """Incidence graph of PG(2, d-1) when d-1 is a prime power and D = 3 (Moore-optimal)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over metacyclic groups Z_m x| Z_k.
#
# Vertices: A_g = g and B_h = G + h for g, h in the group (identity coded 0).
# Connection set S (size d, containing identity WLOG): A_g ~ B_{g*s} for s in S.
# Left multiplication is an automorphism, so distances only need to be measured
# from A_e and B_e. A zero-cost pair of sources means the graph has diameter <= D.
# ----------------------------------------------------------------------------

def _groups_of_order(G):
    """All (m, k, r) with m*k = G giving a semidirect product Z_m x| Z_k (r = 1 for abelian)."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if k == 1:
            out.append((m, 1, 1))
            continue
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(G, m, k, r):
    """R[x][g] = g*x (right multiplication) and Ri[x][h] = h*x^{-1}."""
    _, mul, inv = lib.semidirect_group(m, k, r)
    R = [[mul(g, x) for g in range(G)] for x in range(G)]
    I = [inv(x) for x in range(G)]
    Ri = [R[I[x]] for x in range(G)]
    return R, Ri


def _bad(G, D, S, R, Ri):
    """Unreached (source, vertex) pairs within distance D from A_e and B_e. Zero means valid."""
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    for s in S:
                        v = G + R[s][u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    h = u - G
                    for s in S:
                        v = Ri[s][h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
    return total


def _climb(G, d, D, R, Ri, rng, deadline, iters):
    """Annealed single-element replacement search over connection sets S containing 0."""
    if d - 1 > G - 1:
        return None
    S = [0] + rng.sample(range(1, G), d - 1)
    c = _bad(G, D, S, R, Ri)
    T = 1.0
    for it in range(iters):
        if c == 0:
            return S
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        x = rng.randrange(1, G)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _bad(G, D, S, R, Ri)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
        else:
            S[i] = old
        T = max(0.3, T * 0.999)
    return S if c == 0 else None


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def _build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + SEARCH_FRAC * time_limit

    base = _safe(d, D)
    if D <= 2 or d <= 2:
        return base

    pg = _pg_case(d, D)
    if pg is not None and lib.is_valid(pg[0], pg[1], d, D):
        return pg

    moore = lib.moore_bound(d, D)
    rng = random.Random(seed * 1000003 + 97 * d + D)
    best = base
    G = best[0] // 2 + 1          # target half-order: each success raises it by one
    cache = {}

    while time.monotonic() < deadline and 2 * G <= moore:
        groups = _groups_of_order(G)
        found = None
        while time.monotonic() < deadline and found is None:
            key = rng.choice(groups)
            if key not in cache:
                cache[key] = _tables(G, *key)
            R, Ri = cache[key]
            S = _climb(G, d, D, R, Ri, rng, deadline, CLIMB_ITERS)
            if S is not None:
                edges = [(g, G + R[s][g]) for s in S for g in range(G)]
                if lib.is_valid(2 * G, edges, d, D):
                    found = (2 * G, edges)
        if found is None:
            break
        best = found
        G += 1

    return best


def build(d, D, seed, time_limit):
    try:
        n, edges = _build(d, D, seed, time_limit)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return _safe(d, D)
