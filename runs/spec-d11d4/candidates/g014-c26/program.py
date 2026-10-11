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
# Twin blow-up of a base graph of degree d-1.
#
# Blowing a vertex v up into two independent twins (same neighbourhood) keeps
# bipartiteness and the diameter. Copies of u get degree sum_{v in N(u)} m_v,
# so each base vertex may have at most one neighbour in S = {v : m_v = 2}.
# Equivalently S has no two vertices at distance 2. Conflicts only join vertices
# on the same colour class of a bipartite base, so the two classes can be
# optimised independently.
#
# NEW SEARCH: instead of iterated local search over the whole conflict graph,
# each class is solved by a fixed-k tabu search. We ask for an independent set
# of size k, minimise the number of conflicting pairs by swapping vertices, and
# increase k whenever zero conflicts are reached. Blow-ups are always checked
# with lib.is_valid, so a bad result simply falls back to a smaller graph.
# ----------------------------------------------------------------------------

def _find_k(nbl, m, k, init, deadline, rng, nprng):
    """Tabu search for an independent set of size k. Returns local indices or None."""
    if k > m:
        return None
    inS = np.zeros(m, dtype=bool)
    cnt = np.zeros(m, dtype=np.int64)     # number of chosen neighbours of each vertex
    tabu = np.zeros(m, dtype=np.int64)
    st = {"f": 0, "size": 0}              # f = number of conflicting pairs in S

    def add(v):
        st["f"] += int(cnt[v])
        cnt[nbl[v]] += 1
        inS[v] = True
        st["size"] += 1

    def remove(u):
        st["f"] -= int(cnt[u])
        cnt[nbl[u]] -= 1
        inS[u] = False
        st["size"] -= 1

    for v in init:
        add(v)
    while st["size"] < k:
        sc = cnt.astype(float) + nprng.random(m)
        sc[inS] = np.inf
        add(int(np.argmin(sc)))

    it = 0
    while st["f"] > 0:
        it += 1
        if (it & 63) == 0 and time.monotonic() >= deadline:
            return None
        Sarr = np.flatnonzero(inS)
        sc = cnt[Sarr].astype(float) + nprng.random(len(Sarr))
        sc[tabu[Sarr] > it] -= 1000.0
        u = int(Sarr[int(np.argmax(sc))])
        remove(u)
        tabu[u] = it + 7 + rng.randrange(10)
        vs = cnt.astype(float) + nprng.random(m)
        vs[inS] = np.inf
        vs[tabu > it] = np.inf
        v = int(np.argmin(vs))
        if np.isinf(vs[v]):
            v = u
        add(v)
    return [int(x) for x in np.flatnonzero(inS)]


def _solve_class(nbl, m, deadline, rng, nprng):
    """Grow a conflict-free set by increasing k until the deadline."""
    best = []
    k = 1
    while time.monotonic() < deadline:
        res = _find_k(nbl, m, k, best, deadline, rng, nprng)
        if res is None:
            break
        best = res
        k = len(best) + 1
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


def _blowup(n0, edges0, d, deadline, rng, nprng):
    """Twin blow-up of a bipartite base of degree d-1 by a large distance-2-free set."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None

    color = [-1] * n0
    for s in range(n0):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if color[w] == -1:
                    color[w] = 1 - color[u]
                    stack.append(w)
                elif color[w] == color[u]:
                    return None

    cs = [set() for _ in range(n0)]
    for w in range(n0):
        a = adj[w]
        for i in range(len(a)):
            for j in range(i + 1, len(a)):
                cs[a[i]].add(a[j])
                cs[a[j]].add(a[i])

    now = time.monotonic()
    mid = now + (deadline - now) * 0.5
    S = []
    for c, dl in ((0, mid), (1, deadline)):
        verts = [v for v in range(n0) if color[v] == c]
        local = {v: i for i, v in enumerate(verts)}
        m = len(verts)
        nbl = [np.array(sorted(local[w] for w in cs[v]), dtype=np.int64) for v in verts]
        sol = _solve_class(nbl, m, dl, rng, nprng)
        S.extend(verts[i] for i in sol)
    return _blow(n0, edges0, S)


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
            res = _blowup(n0, e0, d, deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
