import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Small baseline families.
# ----------------------------------------------------------------------------

def _k_dd(d):
    """K_{d,d}: diameter 2, always valid for D >= 2."""
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 23), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
# New construction: bi-Cayley graphs over metacyclic groups Z_m x| Z_k.
#
# Vertices: A_g = g and B_x = G + x for g, x in the group of order G.
# Connection set S (|S| = d, with the identity 0 always in S):
#   A_g is joined to B_{g*s} for every s in S.
# Left multiplication is an automorphism, so the A-side and B-side are each
# vertex-transitive. Diameter <= D therefore only needs two BFS runs, from A_e
# and from B_e. This lets the search cover many non-cyclic groups quickly.
# ----------------------------------------------------------------------------

def _group_table(m, k, r):
    """Multiplication table and inverse list for lib.semidirect_group(m, k, r)."""
    order, mul, _ = lib.semidirect_group(m, k, r)
    tab = [[mul(x, y) for y in range(order)] for x in range(order)]
    inv = [row.index(0) for row in tab]  # right inverse; equals inverse in a group
    return order, tab, inv


def _sample_group(G, rng):
    """Random metacyclic group of order G as (order, tab, inv), or None."""
    divs = [m for m in range(1, G + 1) if G % m == 0]
    for _ in range(30):
        m = rng.choice(divs)
        k = G // m
        if m == 1:
            r = 0
        else:
            cands = []
            for _ in range(60):
                r = rng.randrange(1, m)
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    cands.append(r)
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            return _group_table(m, k, r)
        except ValueError:
            continue
    return None


def _reach_bad(G, tab, inv, S, invS, D, src):
    """Number of vertices of the bi-Cayley graph not within distance D of src."""
    N = 2 * G
    seen = bytearray(N)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < G:
                row = tab[u]
                for s in S:
                    v = G + row[s]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                row = tab[u - G]
                for si in invS:
                    v = row[si]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        if not nxt:
            break
        cnt += len(nxt)
        frontier = nxt
    return N - cnt


def _cost(G, tab, inv, S, D):
    invS = [inv[s] for s in S]
    return _reach_bad(G, tab, inv, S, invS, D, 0) + _reach_bad(G, tab, inv, S, invS, D, G)


def _climb(G, tab, inv, d, D, rng, iters, deadline):
    """Simulated annealing over S (|S| = d, identity included). Returns S or None."""
    if G < d or d < 2:
        return None
    S = [0] + rng.sample(range(1, G), d - 1)
    c = _cost(G, tab, inv, S, D)
    T = 1.0
    for it in range(iters):
        if c == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        new = rng.randrange(1, G)
        if new in S:
            continue
        S2 = S[:]
        S2[i] = new
        c2 = _cost(G, tab, inv, S2, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = S2, c2
        T = max(0.1, T * 0.999)
    return S if c == 0 else None


def _cayley_edges(G, tab, S):
    E = []
    for g in range(G):
        row = tab[g]
        for s in S:
            E.append((g, G + row[s]))
    return 2 * G, E


def _cayley_search(d, D, best_n, consider, deadline, rng):
    """Search for bi-Cayley graphs of order 2G with G just above the current best half-order."""
    lo = max(best_n // 2 + 1, d)
    while time.monotonic() < deadline:
        G = rng.randint(lo, lo + max(4, lo // 30))
        if G > 1200:
            break
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, tab, inv = g
        slice_end = min(deadline, time.monotonic() + 3.0)
        S = _climb(order, tab, inv, d, D, rng, 4000, slice_end)
        if S is not None:
            n, e = _cayley_edges(order, tab, S)
            if consider(n, e):
                lo = max(lo, n // 2 + 1)
            else:
                lo = max(lo, order + 1)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * time_limit, time_limit - 6.0)
    deadline = start + max(0.5, budget)
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])

    best = _k_dd(d)
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 3 and d >= 2 and best_n < lib.moore_bound(d, D):
        _cayley_search(d, D, best_n, consider, deadline, rng)

    if not lib.is_valid(best[0], best[1], d, D):
        best = _k_dd(d)
    return best
