import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: projective plane (D >= 3) and generalized quadrangle W(q)
# (D >= 4). Both are checked with lib.is_valid before use.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW family for D >= 5: exhaustive bi-Cayley graphs over semidirect products.
#
# Group G = Z_m x| Z_k (order m*k), connection set S of size d.
# Vertices: A_g = g and B_h = G + h. Edges: A_g ~ B_{g*s} for s in S.
# This is a bi-regular graph of degree d on 2|G| vertices. Left multiplication
# is an automorphism transitive on each side, so two BFS runs (from A_e and
# from B_e) certify the diameter.
#
# Unlike the parent's random dart search, this enumerates EVERY semidirect
# structure of a given order, and the search window is anchored just above
# the current best order, so each success raises the target.
# ----------------------------------------------------------------------------

def _group_list(G, rng, cap=40):
    """All (m, k, r) with m*k = G giving semidirect products Z_m x| Z_k (shuffled, capped)."""
    groups = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            groups.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                groups.append((m, k, r))
    rng.shuffle(groups)
    return groups[:cap]


def _table(m, k, r):
    """Full multiplication and inverse tables for the semidirect product, or None."""
    try:
        G, mul, inv = lib.semidirect_group(m, k, r)
    except ValueError:
        return None
    T = [[mul(x, y) for y in range(G)] for x in range(G)]
    I = [inv(x) for x in range(G)]
    return G, T, I


def _cost(S, G, T, I, D, limit=float("inf")):
    """Number of (source, vertex) pairs at distance > D from A_e and from B_e."""
    N = 2 * G
    inv_S = [I[s] for s in S]
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
                    for si in inv_S:
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


def _anneal(G, T, I, d, D, rng, deadline, max_iters):
    """Anneal a size-d connection set S in G. Returns (S or None, best cost)."""
    S = rng.sample(range(G), d)
    cur = _cost(S, G, T, I, D)
    best, best_S = cur, list(S)
    temp = 2.0
    it = 0
    while cur > 0 and it < max_iters and time.monotonic() < deadline:
        it += 1
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c = _cost(S, G, T, I, D, limit=cur + 40 * temp)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
            if cur < best:
                best, best_S = cur, list(S)
        else:
            S[i] = old
        temp = max(0.3, temp * 0.999)
    return (best_S if best == 0 else None), best


def _bicayley_edges(G, T, S):
    """Edge list of the bi-Cayley graph (2G vertices)."""
    E = []
    for g in range(G):
        row = T[g]
        for s in S:
            E.append((g, G + row[s]))
    return 2 * G, E


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D >= 5:
        group_cache = {}
        while time.monotonic() < deadline and best_n < lib._moore_bound(d, D):
            lo = best_n // 2 + 1
            G = rng.randint(lo, lo + 20)
            if G < d:
                continue
            if G not in group_cache:
                group_cache[G] = _group_list(G, rng)
            groups = group_cache[G]
            if not groups:
                continue
            m, k, r = groups.pop()
            tab = _table(m, k, r)
            if tab is None:
                continue
            Gt, T, I = tab
            if Gt < d:
                continue
            anneal_deadline = min(deadline, time.monotonic() + 2.0)
            S, _ = _anneal(Gt, T, I, d, D, rng, anneal_deadline, 3000)
            if S is not None:
                n, e = _bicayley_edges(Gt, T, S)
                consider(n, e)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
