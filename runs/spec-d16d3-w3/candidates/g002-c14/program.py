import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley (Haar-type) graphs over a finite group G of order m.
#
# A_x is joined to B_{s x} for every s in S (|S| = d, identity 0 in S WLOG).
# Right multiplication by h is an automorphism, so the graph is "transitive"
# on each side. For diameter 3 the conditions are:
#   S^{-1} S = G   (A-A pairs at distance 2)
#   S S^{-1} = G   (B-B pairs at distance 2)
# and A-B pairs are then automatically within distance 3 (S S^{-1} S = G).
# So the search is a fast difference-covering problem.
# ----------------------------------------------------------------------------

def _haar(m, T, S):
    """Edges of the bi-Cayley graph: A_x = x, B_z = m + z, A_x ~ B_{T[s][x]}."""
    edges = [(x, m + T[s][x]) for s in S for x in range(m)]
    return 2 * m, edges


def _diff_cost(m, T, invl, S):
    """Number of group elements missed by S^{-1}S together with those missed by S S^{-1}."""
    L = set()
    R = set()
    for s in S:
        row_inv = T[invl[s]]
        row = T[s]
        for t in S:
            L.add(row_inv[t])        # s^{-1} t
            R.add(row[invl[t]])      # s t^{-1}
    return 2 * m - len(L) - len(R)


def _groups_of_order(m, rng):
    """Cyclic group plus several semidirect products Z_a x| Z_b with a*b = m; returns (mul, inv) pairs."""
    groups = []
    _, mul, inv = lib.cyclic_group(m)
    groups.append((mul, inv))
    for b in range(2, m):
        if m % b:
            continue
        a = m // b
        if a < 2:
            continue
        rs = [r for r in range(1, a) if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a]
        rng.shuffle(rs)
        for r in rs[:4]:
            try:
                _, mul2, inv2 = lib.semidirect_group(a, b, r)
            except ValueError:
                continue
            groups.append((mul2, inv2))
    rng.shuffle(groups)
    return groups


def _table(m, mul, inv):
    """Full multiplication table and inverse list for a group with identity 0."""
    T = [[mul(x, y) for y in range(m)] for x in range(m)]
    invl = [inv(x) for x in range(m)]
    return T, invl


def _search(m, T, invl, d, rng, deadline, D):
    """Annealed search for a connection set S (|S| = d, 0 in S) giving a valid bi-Cayley graph."""
    if d > m:
        return None

    if D == 3:
        def cost(S):
            return _diff_cost(m, T, invl, S)
    else:
        def cost(S):
            n, e = _haar(m, T, S)
            return lib.bad_pairs(n, e, D)

    S = [0] + rng.sample(range(1, m), d - 1)
    cur = cost(S)
    best_c = cur
    stall = 0
    temp = 0.6
    while time.monotonic() < deadline:
        if cur == 0:
            return S
        stall += 1
        if stall > 3000:
            # Restart from a fresh random set after a long plateau.
            S = [0] + rng.sample(range(1, m), d - 1)
            cur = cost(S)
            best_c = cur
            stall = 0
            continue
        i = rng.randrange(1, d)
        new = rng.randrange(1, m)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c = cost(S)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
            if c < best_c:
                best_c = c
                stall = 0
        else:
            S[i] = old
    return S if cur == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    rng = random.Random(seed * 1000003 + d * 131 + D)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, order 2d, diameter 2 (optimal for D = 2).
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    # D >= 3: projective plane incidence graph (diameter 3) as a stronger baseline.
    try:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    except Exception:
        pass

    # New family: bi-Cayley graphs over cyclic / semidirect groups, found by a
    # difference-covering search. Each success raises the group order by one.
    try:
        upper = (d * d - d + 1) if D == 3 else lib.moore_bound(d, D) // 2
        m = best[0] // 2 + 1
        while m <= upper and time.monotonic() < deadline:
            groups = _groups_of_order(m, rng)
            found = None
            T = invl = None
            gi = 0
            while time.monotonic() < deadline and found is None and groups:
                mul, inv = groups[gi % len(groups)]
                gi += 1
                T, invl = _table(m, mul, inv)
                tl = min(deadline, time.monotonic() + 4.0)
                S = _search(m, T, invl, d, rng, tl, D)
                if S:
                    found = S
            if found is None:
                break
            n, e = _haar(m, T, found)
            consider(n, e)
            m += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
