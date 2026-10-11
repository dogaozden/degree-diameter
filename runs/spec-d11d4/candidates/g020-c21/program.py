import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bases.
# ----------------------------------------------------------------------------

def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq(q):
    """Point-line incidence graph of the symplectic generalized quadrangle W(q).

    Points are 0..P-1, lines are P..P+L-1. Every point lies on q+1 lines, every
    line has q+1 points, and the incidence graph has diameter 4.
    """
    F = lib.GF(q)
    A = F.add_table.tolist()
    M = F.mul_table.tolist()
    NEG = [F.neg(a) for a in range(q)]
    INV = [0] + [F.inv(a) for a in range(1, q)]
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    P = len(pts)
    index = {v: i for i, v in enumerate(pts)}

    def norm(v):
        c = next(x for x in v if x)
        ic = INV[c]
        return tuple(M[ic][x] for x in v)

    covered = [bytearray(P) for _ in range(P)]
    lines = []
    for i in range(P):
        x = pts[i]
        ci = covered[i]
        for j in range(i + 1, P):
            if ci[j]:
                continue
            y = pts[j]
            # Symplectic form x0*y1 - x1*y0 + x2*y3 - x3*y2.
            t = A[M[x[0]][y[1]]][NEG[M[x[1]][y[0]]]]
            s = A[M[x[2]][y[3]]][NEG[M[x[3]][y[2]]]]
            if A[t][s] != 0:
                continue
            L = set()
            for a in range(q):
                ax = [M[a][x[k]] for k in range(4)]
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(A[ax[k]][M[b][y[k]]] for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                cp = covered[p]
                for r in L:
                    cp[r] = 1
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return P + len(lines), edges


# ----------------------------------------------------------------------------
# Twin blow-up with a distance-2-free vertex set.
#
# If every vertex of a base graph G has degree d-1, replace some vertices v by
# two copies sharing the same neighbourhood. Each copy of u then has degree
# sum_{v in N(u)} m_v, which is at most d iff u has at most one neighbour in
# S = {v : m_v = 2}. So S must have no two vertices at distance 2. The blow-up
# keeps bipartiteness and diameter, giving n0 + |S| vertices.
#
# For W(q) the conflicts are collinear points and concurrent lines, so S is a
# partial ovoid plus a partial spread. This is a maximum independent set problem
# on the conflict graph.
#
# NEW: replace the plain tabu local search with an ARW-style iterated local
# search. It uses (1,2)-swaps (remove one vertex, insert two non-adjacent
# vertices that were blocked only by it) and perturbation by forced insertion.
# It is stronger on these dense conflict graphs, so the independent set should
# grow past the previous 133.
# ----------------------------------------------------------------------------

def _mis(N, nb, rng, deadline):
    """Iterated local search (ARW style) for a large independent set."""
    adjs = [set(x) for x in nb]
    insol = [False] * N
    tight = [0] * N              # number of solution neighbours
    tabu = [0] * N
    S = set()
    cand = list(range(N))        # vertices that may have become free

    def add(v):
        insol[v] = True
        S.add(v)
        for u in nb[v]:
            tight[u] += 1

    def rem(v):
        insol[v] = False
        S.discard(v)
        for u in nb[v]:
            tight[u] -= 1
        cand.extend(nb[v])
        cand.append(v)

    def local():
        while True:
            while cand:
                v = cand.pop()
                if not insol[v] and tight[v] == 0:
                    add(v)
            found = False
            for x in list(S):
                if not insol[x]:
                    continue
                L = [u for u in nb[x] if tight[u] == 1]
                if len(L) < 2:
                    continue
                pair = None
                for i in range(len(L)):
                    ai = adjs[L[i]]
                    for j in range(i + 1, len(L)):
                        if L[j] not in ai:
                            pair = (L[i], L[j])
                            break
                    if pair:
                        break
                if pair:
                    rem(x)
                    add(pair[0])
                    add(pair[1])
                    found = True
            if not found:
                break

    local()
    best = list(S)
    it = 0
    while time.monotonic() < deadline:
        it += 1
        # Choose a non-solution vertex with few solution neighbours (sampled).
        bv, bt = -1, 1 << 30
        for _ in range(8):
            v = rng.randrange(N)
            if insol[v] or tabu[v] > it:
                continue
            if tight[v] < bt:
                bt = tight[v]
                bv = v
        if bv < 0:
            continue
        for u in [u for u in nb[bv] if insol[u]]:
            rem(u)
            tabu[u] = it + 7
        add(bv)
        local()
        if len(S) > len(best):
            best = list(S)
        elif len(S) < len(best) - 2:
            # Drifted too far below the best: restore it.
            for v in list(S):
                rem(v)
            for v in best:
                add(v)
            local()
    return best


def _blow(n0, edges0, S):
    """Blow up each vertex of S into two twin copies (same neighbourhood)."""
    extra = {}
    for v in S:
        extra[v] = n0 + len(extra)
    copies = [[v] + ([extra[v]] if v in extra else []) for v in range(n0)]
    edges = []
    for u, v in edges0:
        for a in copies[u]:
            for b in copies[v]:
                edges.append((a, b))
    return n0 + len(extra), edges


def _blowup(n0, edges0, d, deadline, rng):
    """Twin blow-up of a base graph of degree d-1 by a large distance-2-free set."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None
    cs = [set() for _ in range(n0)]
    for w in range(n0):
        a = adj[w]
        for i in range(len(a)):
            for j in range(i + 1, len(a)):
                x, y = a[i], a[j]
                cs[x].add(y)
                cs[y].add(x)
    nb = [sorted(s) for s in cs]
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)
    S = _mis(n0, nb, rng, deadline)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    # Use more of the budget for search (the scorer allows time_limit).
    deadline = start + max(0.5, 0.85 * time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    pg = _pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Blow-up route: base of degree exactly d-1 with q = d-2 a prime power.
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        else:
            n0, e0 = 0, []
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, deadline, rng)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
