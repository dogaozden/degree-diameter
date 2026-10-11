import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley (Haar-type) graphs over matrix groups SL(2,p) and PSL(2,p).
#
# Vertices: A_g = g and B_h = G + h for group elements g, h.
# Edges:    A_g ~ B_{g*s} for every s in S, |S| = d.
#
# Left multiplication by any group element is an automorphism and preserves
# both sides, so the graph is bipartite and d-regular, and it is valid iff the
# BFS balls of radius D around A_e and B_e cover the whole vertex set.
# This is a different family from the cyclic and semidirect lifts: the groups
# are non-solvable, which makes the random search far less likely to be
# trapped by abelian collisions.
#
# Search: simulated annealing over the connection set S, with the cost equal to
# the number of vertices unreached within distance D from A_e and B_e.
# ----------------------------------------------------------------------------

def _code(a, b, c, e, p):
    return ((a * p + b) * p + c) * p + e


def _sl2_reps(p, quotient):
    """Representatives of SL(2,p), or of PSL(2,p) = SL(2,p)/{+-I} when quotient is True."""
    reps = []
    for a in range(p):
        for b in range(p):
            for c in range(p):
                for e in range(p):
                    if (a * e - b * c) % p != 1:
                        continue
                    if quotient:
                        if _code(a, b, c, e, p) > _code((-a) % p, (-b) % p, (-c) % p, (-e) % p, p):
                            continue
                    reps.append((a, b, c, e))
    return reps


def _matrix_group(p, quotient):
    """Return (G, mul, inv, identity_index) for SL(2,p) or PSL(2,p), or None on failure."""
    reps = _sl2_reps(p, quotient)
    G = len(reps)
    lookup = np.full(p ** 4, -1, dtype=np.int64)
    for i, (a, b, c, e) in enumerate(reps):
        lookup[_code(a, b, c, e, p)] = i
        if quotient:
            lookup[_code((-a) % p, (-b) % p, (-c) % p, (-e) % p, p)] = i
    R = np.array(reps, dtype=np.int64)
    a, b, c, e = R[:, 0], R[:, 1], R[:, 2], R[:, 3]
    pa = (a[:, None] * a[None, :] + b[:, None] * c[None, :]) % p
    pb = (a[:, None] * b[None, :] + b[:, None] * e[None, :]) % p
    pc = (c[:, None] * a[None, :] + e[:, None] * c[None, :]) % p
    pd = (c[:, None] * b[None, :] + e[:, None] * e[None, :]) % p
    code = ((pa * p + pb) * p + pc) * p + pd
    mul = lookup[code]
    if (mul < 0).any():
        return None
    ident = int(lookup[_code(1, 0, 0, 1, p)])
    if ident < 0:
        return None
    inv = np.argmax(mul == ident, axis=1).astype(np.int64)
    return G, mul, inv, ident


def _cost(G, mul, S, Sinv, e, D):
    """Number of (vertex, source) pairs not within distance D, sources A_e and B_e."""
    total = 0
    for src in (0, 1):
        vis = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
        vis[src][e] = True
        frontier = np.array([e], dtype=np.int64)
        cur = src
        for _ in range(D):
            if frontier.size == 0:
                break
            idx = S if cur == 0 else Sinv
            block = mul[np.ix_(frontier, idx)].ravel()
            nxt = np.zeros(G, dtype=bool)
            nxt[block] = True
            nxt &= ~vis[1 - cur]
            vis[1 - cur] |= nxt
            frontier = np.flatnonzero(nxt)
            cur = 1 - cur
        total += 2 * G - int(vis[0].sum()) - int(vis[1].sum())
    return total


def _sa(tab, d, D, rng, iters, deadline):
    """Simulated annealing on the connection set. Returns (best_cost, best_S)."""
    G, mul, inv, e = tab
    elems = rng.sample(range(G), d)
    S = np.array(elems, dtype=np.int64)
    cost = _cost(G, mul, S, inv[S], e, D)
    best_cost, best_S = cost, S
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, 2.0 * (1.0 - t / iters))
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in elems:
            continue
        elems2 = elems.copy()
        elems2[i] = x
        S2 = np.array(elems2, dtype=np.int64)
        c2 = _cost(G, mul, S2, inv[S2], e, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            elems, S, cost = elems2, S2, c2
            if cost < best_cost:
                best_cost, best_S = cost, S
    return best_cost, best_S


def _edges(G, mul, S):
    """Edge list of the bi-Cayley graph with connection set S."""
    out = []
    for s in S:
        col = mul[:, int(s)]
        out.extend((g, G + int(col[g])) for g in range(G))
    return 2 * G, out


def _group_order(p, quotient):
    o = p * (p * p - 1)
    return o // 2 if quotient else o


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.9 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D <= 2 or d < 2:
        return best

    # Bi-Cayley search over non-solvable matrix groups.
    moore = lib._moore_bound(d, D)
    specs = []
    for p in (5, 7, 11, 13):
        for quotient in (True, False):
            order = _group_order(p, quotient)
            n_spec = 2 * order
            if order < d or n_spec <= best_n or n_spec > moore:
                continue
            specs.append((n_spec, p, quotient))
    specs.sort()  # smaller first, so a valid record-beating graph is secured early

    tables = {}
    active = list(specs)
    while active and time.monotonic() < deadline:
        for spec in list(active):
            if time.monotonic() >= deadline:
                break
            n_spec, p, quotient = spec
            if n_spec <= best_n:
                active.remove(spec)
                continue
            if spec not in tables:
                tables[spec] = _matrix_group(p, quotient)
            tab = tables[spec]
            if tab is None:
                active.remove(spec)
                continue
            cost, S = _sa(tab, d, D, rng, 2500, deadline)
            if cost == 0:
                n2, e2 = _edges(tab[0], tab[1], S)
                consider(n2, e2)
                active.remove(spec)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
