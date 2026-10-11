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
# Twin blow-up.
#
# Blowing a vertex v up into two twins (same neighbourhood) preserves all
# distances between original vertices, so the diameter is unchanged. A vertex u
# of base degree d-1 gains one degree per blown neighbour, so it may have at most
# one blown neighbour. Per side of the bipartition this means:
#   - the blown A-vertices have pairwise disjoint neighbourhoods (partial spread);
#   - the blown B-vertices have no common neighbour (partial ovoid).
# The two constraints are independent, so the sides are searched separately.
# ----------------------------------------------------------------------------

def _spread_search(A_nb, B_to_A, nB, k, rng, deadline):
    """Largest family of A-vertices with pairwise disjoint neighbourhoods (k each).

    Depth-first search that always branches on the uncovered B-vertex with the
    fewest available A-options. Restarts with fresh random orders on node caps.
    """
    nA = len(A_nb)
    blocked = [0] * nA
    covered = [False] * nB
    chosen = []
    best = []
    stop = [False]
    steps = [0]
    cap = [0]
    order = list(range(nB))

    def rec(U):
        if stop[0]:
            return
        steps[0] += 1
        if steps[0] > cap[0] or ((steps[0] & 15) == 0 and time.monotonic() >= deadline):
            stop[0] = True
            return
        if len(chosen) > len(best):
            best[:] = chosen
        if U == 0 or len(chosen) + U // k <= len(best):
            return
        pick = None
        for b in order:
            if covered[b]:
                continue
            o = [a for a in B_to_A[b] if blocked[a] == 0]
            if not o:
                return
            if pick is None or len(o) < len(pick):
                pick = o
        rng.shuffle(pick)
        for a in pick:
            chosen.append(a)
            for x in A_nb[a]:
                covered[x] = True
                for a2 in B_to_A[x]:
                    blocked[a2] += 1
            rec(U - k)
            for x in A_nb[a]:
                covered[x] = False
                for a2 in B_to_A[x]:
                    blocked[a2] -= 1
            chosen.pop()
            if stop[0]:
                return

    while time.monotonic() < deadline and len(best) * k < nB:
        rng.shuffle(order)
        stop[0] = False
        cap[0] = steps[0] + 600
        rec(nB)
    return list(best)


def _ils_independent(N, nb, rng, deadline):
    """Maximum-independent-set search: (1,2)-swap local search with perturbation.

    Maintains an independent set S and, for each vertex, its number of S-neighbours
    ("tightness"). A (1,2)-swap removes one vertex x of S and inserts two
    non-adjacent vertices whose only S-neighbour is x. Perturbation forces a random
    outside vertex into S; the search falls back to the best set when it drifts.
    """
    if N == 0:
        return []
    adjs = [set(x) for x in nb]
    inS = [False] * N
    tight = [0] * N
    S = set()

    def ins(v):
        inS[v] = True
        S.add(v)
        for w in nb[v]:
            tight[w] += 1

    def rem(v):
        inS[v] = False
        S.discard(v)
        for w in nb[v]:
            tight[w] -= 1

    def fill():
        free = [v for v in range(N) if not inS[v] and tight[v] == 0]
        rng.shuffle(free)
        for v in free:
            if not inS[v] and tight[v] == 0:
                ins(v)

    def two_improve():
        improved = True
        while improved and time.monotonic() < deadline:
            improved = False
            order = list(S)
            rng.shuffle(order)
            for x in order:
                if not inS[x]:
                    continue
                L = [w for w in nb[x] if tight[w] == 1]
                if len(L) < 2:
                    continue
                rng.shuffle(L)
                pair = None
                for i in range(len(L)):
                    a = L[i]
                    aa = adjs[a]
                    for j in range(i + 1, len(L)):
                        if L[j] not in aa:
                            pair = (a, L[j])
                            break
                    if pair:
                        break
                if pair:
                    rem(x)
                    ins(pair[0])
                    ins(pair[1])
                    fill()
                    improved = True

    fill()
    two_improve()
    best = list(S)
    best_size = len(S)
    while time.monotonic() < deadline:
        v = rng.randrange(N)
        if inS[v]:
            continue
        for w in nb[v]:
            if inS[w]:
                rem(w)
        ins(v)
        fill()
        two_improve()
        if len(S) > best_size:
            best = list(S)
            best_size = len(S)
        elif len(S) < best_size - 1 or rng.random() < 0.02:
            for u in list(S):
                rem(u)
            for u in best:
                ins(u)
    return best


def _two_colour(n, edges):
    """Return a 0/1 colouring of a bipartite graph (vertices in each component start at 0)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    stack.append(y)
    return color


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
    """Twin blow-up of a base graph of degree d-1.

    Side A (one colour class) gets a partial spread by DFS exact cover. Side B gets
    a large conflict-free set by the (1,2)-swap ILS over its collinearity graph.
    """
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)
    color = _two_colour(n0, edges0)
    sides = [[v for v in range(n0) if color[v] == c] for c in (0, 1)]

    now = time.monotonic()
    total = max(0.0, deadline - now)

    # Side A: partial spread (disjoint neighbourhoods in B).
    A_list = sides[1]
    B_list = sides[0]
    idxB = {v: i for i, v in enumerate(B_list)}
    A_nb = [[idxB[w] for w in adj[v]] for v in A_list]
    B_to_A = [[] for _ in B_list]
    for ai, nbs in enumerate(A_nb):
        for b in nbs:
            B_to_A[b].append(ai)
    res = _spread_search(A_nb, B_to_A, len(B_list), d - 1, rng, now + 0.35 * total)
    S = [A_list[ai] for ai in res]

    # Side B: partial ovoid. Conflict = sharing a neighbour in A.
    V = sides[0]
    idx = {v: i for i, v in enumerate(V)}
    conf = [set() for _ in V]
    for w in sides[1]:
        pts = [idx[x] for x in adj[w]]
        for a in pts:
            ca = conf[a]
            for b in pts:
                if a != b:
                    ca.add(b)
    nb = [sorted(s) for s in conf]
    res2 = _ils_independent(len(V), nb, rng, deadline)
    S += [V[i] for i in res2]
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
