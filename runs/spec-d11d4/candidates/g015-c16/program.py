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
# Twin blow-up of a degree-(d-1) base graph by a distance-2-free vertex set S.
# Copies of u get degree 10 + |N(u) ∩ S| for W(q), so |N(u) ∩ S| <= 1 is needed
# (for general base degree d-1: the set S must be independent in the
# distance-2 conflict graph). Bipartiteness and diameter are preserved.
# ----------------------------------------------------------------------------

def _mis(N, nb, rng, deadline):
    """Maximum-ish independent set via (1,2)-swap local search with perturbation.

    nb[v] is the list of conflict-neighbours of v. Returns a list of vertices.
    """
    adjs = [set(x) for x in nb]
    inS = [False] * N
    tight = [0] * N
    S = set()

    def ins(v):
        inS[v] = True
        S.add(v)
        for u in nb[v]:
            tight[u] += 1

    def rem(v):
        inS[v] = False
        S.discard(v)
        for u in nb[v]:
            tight[u] -= 1

    order = list(range(N))
    rng.shuffle(order)
    for v in order:
        if not inS[v] and tight[v] == 0:
            ins(v)

    def two_improve():
        improved = True
        while improved:
            improved = False
            for x in list(S):
                if not inS[x]:
                    continue
                L = [u for u in nb[x] if tight[u] == 1]
                if len(L) < 2:
                    continue
                rng.shuffle(L)
                found = None
                for i in range(len(L)):
                    a = L[i]
                    for j in range(i + 1, len(L)):
                        b = L[j]
                        if b not in adjs[a]:
                            found = (a, b)
                            break
                    if found:
                        break
                if found:
                    rem(x)
                    ins(found[0])
                    ins(found[1])
                    for u in nb[x]:
                        if not inS[u] and tight[u] == 0:
                            ins(u)
                    improved = True

    two_improve()
    best = list(S)
    best_size = len(S)
    it = 0
    while time.monotonic() < deadline:
        it += 1
        if len(S) < best_size - 3:
            for v in list(S):
                rem(v)
            for v in best:
                ins(v)
        else:
            v = rng.randrange(N)
            tries = 0
            while inS[v] and tries < 100:
                v = rng.randrange(N)
                tries += 1
            if inS[v]:
                continue
            removed = [u for u in nb[v] if inS[u]]
            for u in removed:
                rem(u)
            ins(v)
            cand = [w for u in removed for w in nb[u]]
            rng.shuffle(cand)
            for w in cand:
                if not inS[w] and tight[w] == 0:
                    ins(w)
        two_improve()
        if len(S) > best_size:
            best = list(S)
            best_size = len(S)
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
    S = _mis(n0, nb, rng, deadline)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.72 * time_limit - 2.0)
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
