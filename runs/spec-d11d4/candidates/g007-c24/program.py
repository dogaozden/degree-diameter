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
# Twin blow-up with a distance-2-free vertex set.
#
# If every vertex of a base graph G has degree d-1, blowing a set S of base
# vertices into twin pairs keeps every degree <= d iff no base vertex has two
# neighbours in S, i.e. S has no two vertices at distance 2. Points of W(q)
# conflict when collinear, lines when concurrent, so S = partial ovoid
# (points) union partial spread (lines), and the two parts do not interact.
#
# Change in this version: a stronger maximum-independent-set search. It uses
# plateau (1,1)-swaps with tabu, free-vertex insertion, and restarts from the
# incumbent with random forced insertions, instead of the earlier plain
# iterated local search.
# ----------------------------------------------------------------------------

def _mis(N, nb, rng, deadline, restart_gap=4000):
    """Search for a large independent set in the conflict graph given by nb."""
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    inS = np.zeros(N, dtype=bool)
    cnt = np.zeros(N, dtype=np.int64)     # number of chosen conflict-neighbours
    tabu = np.zeros(N, dtype=np.int64)
    size = [0]
    best = []
    best_size = 0
    last = 0

    def add(v):
        inS[v] = True
        cnt[nbn[v]] += 1
        size[0] += 1

    def rem(u):
        inS[u] = False
        cnt[nbn[u]] -= 1
        size[0] -= 1

    it = 0
    while True:
        it += 1
        if (it & 127) == 0 and time.monotonic() >= deadline:
            break

        ok = (~inS) & (tabu <= it)

        free = np.flatnonzero(ok & (cnt == 0))
        if free.size:
            add(int(free[rng.randrange(free.size)]))
            if size[0] > best_size:
                best_size = size[0]
                best = np.flatnonzero(inS).tolist()
                last = it
            continue

        one = np.flatnonzero(ok & (cnt == 1))
        if one.size and rng.random() < 0.995:
            # Plateau move: swap a vertex with exactly one conflict in S.
            v = int(one[rng.randrange(one.size)])
            u = next(x for x in nb[v] if inS[x])
            rem(u)
            tabu[u] = it + 7 + rng.randrange(7)
            add(v)
        else:
            # Forced insertion: evict all conflicting members.
            cand = np.flatnonzero(ok)
            if cand.size == 0:
                continue
            v = int(cand[rng.randrange(cand.size)])
            for u in nb[v]:
                if inS[u]:
                    rem(u)
                    tabu[u] = it + 7
            add(v)

        if best_size > 0 and it - last > restart_gap:
            # Restart from the incumbent.
            inS[:] = False
            cnt[:] = 0
            size[0] = 0
            for v in best:
                add(v)
            last = it

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
    deadline = start + max(0.5, 0.8 * time_limit - 4.0)
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
