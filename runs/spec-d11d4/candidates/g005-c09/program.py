import itertools
import random
import time

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
# two copies sharing v's neighbourhood. A vertex u then has degree
# (d-1) + |N(u) cap S|, so S must contain at most one neighbour of each u:
# S is a set of base vertices with no two at distance 2. Blow-ups keep
# bipartiteness and diameter, so each such S yields a valid graph.
#
# NEW IDEA (side decomposition): in a bipartite base graph, two vertices at
# distance 2 lie on the same colour class, so the conflict graph is the disjoint
# union of two graphs, one per colour class. The two independent-set problems
# do not interact, so we solve them separately with dedicated searches, each
# with its own time share and its own stagnation/perturbation clock.
# ----------------------------------------------------------------------------

def _two_colour(n0, edges0):
    """Return (colour list, adjacency lists) for a bipartite base graph."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n0
    for s in range(n0):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col, adj


def _side_conflicts(n0, adj, col, c):
    """Conflict graph on colour class c: two class-c vertices conflict iff they share a neighbour."""
    verts = [v for v in range(n0) if col[v] == c]
    loc = {v: i for i, v in enumerate(verts)}
    cs = [set() for _ in verts]
    for w in range(n0):
        if col[w] == c:
            continue
        a = adj[w]
        for i in range(len(a)):
            x = loc[a[i]]
            for j in range(i + 1, len(a)):
                y = loc[a[j]]
                cs[x].add(y)
                cs[y].add(x)
    return verts, [sorted(s) for s in cs]


def _side_mis(nb, rng, deadline):
    """Tabu-guided iterated local search for a large independent set; returns local indices."""
    N = len(nb)
    if N == 0:
        return []
    cnt = [0] * N        # number of chosen conflict-neighbours of each vertex
    inS = [False] * N
    tabu = [0] * N
    S = []
    conf = 0             # number of conflicting pairs inside S
    best = []
    it = 0
    last = 0

    def add(v):
        nonlocal conf
        conf += cnt[v]
        for x in nb[v]:
            cnt[x] += 1
        inS[v] = True
        S.append(v)

    def rem(u):
        nonlocal conf
        conf -= cnt[u]
        for x in nb[u]:
            cnt[x] -= 1
        inS[u] = False
        S.remove(u)

    def pick():
        m = None
        cands = []
        for v in range(N):
            if inS[v] or tabu[v] > it:
                continue
            s = cnt[v]
            if m is None or s < m:
                m = s
                cands = [v]
            elif s == m:
                cands.append(v)
        if not cands:
            return -1
        return rng.choice(cands)

    while True:
        it += 1
        if (it & 127) == 0 and time.monotonic() >= deadline:
            break
        if conf == 0:
            if len(S) > len(best):
                best = list(S)
                last = it
            v = pick()
            if v >= 0:
                add(v)
        else:
            conflicting = [u for u in S if cnt[u] > 0]
            if conflicting:
                u = rng.choice(conflicting)
                rem(u)
                tabu[u] = it + 7 + rng.randrange(10)
            v = pick()
            if v >= 0:
                add(v)
        if S and it - last > 3000:
            u = rng.choice(S)
            rem(u)
            tabu[u] = it + 5
            last = it
    if conf == 0 and len(S) > len(best):
        best = list(S)
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
    """Twin blow-up of a base graph of degree d-1, solving each colour class separately."""
    col, adj = _two_colour(n0, edges0)
    if any(len(a) != d - 1 for a in adj):
        return None
    t0 = time.monotonic()
    total = max(0.0, deadline - t0)
    if n0 <= 60:
        total = min(total, 2.0)
    chosen = []
    for idx, c in enumerate((0, 1)):
        verts, nb = _side_conflicts(n0, adj, col, c)
        frac = 0.5 if idx == 0 else 1.0
        dl = t0 + total * frac
        loc_best = _side_mis(nb, rng, dl)
        chosen.extend(verts[i] for i in loc_best)
    return _blow(n0, edges0, chosen)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 2.0)
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
