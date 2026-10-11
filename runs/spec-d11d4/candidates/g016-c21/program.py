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
# Twin blow-up, decomposed by bipartition side.
#
# If every vertex of a base graph G has degree d-1, blow up a set S of base
# vertices into twin pairs. A copy of u then has degree 
# (d-1) + |N(u) ∩ S|, so S must have no two vertices at distance 2.
#
# NEW IDEA (this island): distance-2 conflicts never join vertices on opposite
# sides of the bipartition. So S = S_A ∪ S_B where S_A is an independent set in
# the conflict graph of side A and S_B one of side B, and the two problems are
# solved separately. Each side has a counting bound: a conflict-free set on side
# k has at most |other side| / (d-1) vertices (their neighbourhoods are
# disjoint). For W(q) this is q^2+1 on each side, i.e. a partial ovoid and a
# partial spread. The search stops as soon as it reaches that bound, and any
# unused time flows to the other side.
# ----------------------------------------------------------------------------

def _two_sides(n0, adj):
    """2-colouring of a bipartite base graph as two sorted vertex lists, or None."""
    color = [-1] * n0
    for s in range(n0):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    side0 = [v for v in range(n0) if color[v] == 0]
    side1 = [v for v in range(n0) if color[v] == 1]
    return side0, side1


def _side_nb(n0, adj, verts):
    """Local conflict lists on `verts`: two vertices conflict if they share a base neighbour."""
    idx = {v: i for i, v in enumerate(verts)}
    nb = [set() for _ in verts]
    for w in range(n0):
        a = [idx[x] for x in adj[w] if x in idx]
        for i in range(len(a)):
            x = a[i]
            for j in range(i + 1, len(a)):
                y = a[j]
                nb[x].add(y)
                nb[y].add(x)
    return [sorted(s) for s in nb]


def _ils(N, nb, rng, nprng, deadline, target):
    """Iterated local search for a large conflict-free set; stops early at `target`."""
    if target <= 0 or N == 0:
        return []
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    cnt = np.zeros(N, dtype=np.int64)
    inS = np.zeros(N, dtype=bool)
    tabu = np.zeros(N, dtype=np.int64)
    S = []
    conf = 0
    best = []
    it = 0
    last_best_it = 0

    def add(v):
        nonlocal conf
        conf += int(cnt[v])
        cnt[nbn[v]] += 1
        inS[v] = True
        S.append(v)

    def remove(u):
        nonlocal conf
        conf -= int(cnt[u])
        cnt[nbn[u]] -= 1
        inS[u] = False
        S.remove(u)

    def pick():
        score = cnt + nprng.random(N)   # random tie-breaking
        score[inS] = np.inf
        score[tabu > it] = np.inf
        v = int(np.argmin(score))
        return v if np.isfinite(score[v]) else -1

    while True:
        it += 1
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        if conf == 0:
            if len(S) > len(best):
                best = list(S)
                last_best_it = it
                if len(best) >= target:
                    break
            v = pick()
            if v < 0:
                break
            add(v)
        else:
            conflicting = [u for u in S if cnt[u] > 0]
            u = conflicting[rng.randrange(len(conflicting))]
            remove(u)
            tabu[u] = it + 5 + rng.randrange(8)
            v = pick()
            if v >= 0:
                add(v)
        if S and it - last_best_it > 15000:
            u = S[rng.randrange(len(S))]
            remove(u)
            tabu[u] = it + 5
            last_best_it = it
    if conf == 0 and len(S) > len(best):
        best = list(S)
    return best


def _twin_set(n0, edges0, d, deadline, rng, nprng):
    """Conflict-free twin set S, solved side by side, or None if the base is unsuitable."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None
    sides = _two_sides(n0, adj)
    if sides is None:
        return None
    chosen = []
    for k in range(2):
        verts = sides[k]
        other = len(sides[1 - k])
        now = time.monotonic()
        # Side 0 gets half the remaining time; side 1 gets whatever is left.
        dl = now + max(0.2, (deadline - now) / 2.0) if k == 0 else deadline
        target = other // (d - 1)
        nb = _side_nb(n0, adj, verts)
        local = _ils(len(verts), nb, rng, nprng, dl, target)
        chosen.extend(verts[i] for i in local)
    return chosen


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


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 4.0)
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

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
            S = _twin_set(n0, e0, d, deadline, rng, nprng)
            if S:
                n, e = _blow(n0, e0, S)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
