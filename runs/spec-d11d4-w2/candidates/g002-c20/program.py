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
# distances between the other vertices, so the diameter is unchanged. A base
# vertex of degree d-1 may gain one degree per blown neighbour, so it may have
# at most one blown neighbour. Hence, on each side of the bipartition, the blown
# vertices must have pairwise disjoint neighbourhoods. The two sides are
# independent constraints and are searched separately.
#
# Each side is an independent-set problem in the "shares a neighbour" conflict
# graph. It is solved here by an ARW-style iterated local search with
# (1,2)-swaps and perturbation. This replaces the earlier exact-cover DFS,
# which stalled on the spread side.
# ----------------------------------------------------------------------------

def _ils(N, nb, rng, deadline, target):
    """Large independent set in the graph with adjacency lists nb (iterated local search)."""
    if N == 0:
        return []
    adjs = [set(x) for x in nb]
    inS = [False] * N
    tight = [0] * N          # number of solution neighbours of each vertex
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

    def local():
        while True:
            free = [v for v in range(N) if not inS[v] and tight[v] == 0]
            if free:
                ins(free[rng.randrange(len(free))])
                continue
            moved = False
            Sl = list(S)
            rng.shuffle(Sl)
            for x in Sl:
                # Vertices whose only solution neighbour is x.
                L = [u for u in nb[x] if tight[u] == 1]
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
                    moved = True
                    break
            if not moved:
                return

    local()
    best = list(S)
    while len(best) < target and time.monotonic() < deadline:
        v = rng.randrange(N)
        for _ in range(50):
            if not inS[v] and tight[v] <= 2:
                break
            v = rng.randrange(N)
        if inS[v]:
            continue
        for u in nb[v]:
            if inS[u]:
                rem(u)
        ins(v)
        local()
        if len(S) > len(best):
            best = list(S)
        elif len(S) < len(best) - 1 or (len(S) < len(best) and rng.random() < 0.05):
            for u in list(S):
                rem(u)
            for u in best:
                ins(u)
    return best


def _side(V, cs, rng, deadline, target):
    """Large conflict-free subset of one side V, using conflict lists cs."""
    idx = {v: i for i, v in enumerate(V)}
    nb_local = [[idx[w] for w in cs[v] if w in idx] for v in V]
    res = _ils(len(V), nb_local, rng, deadline, target)
    return [V[i] for i in res]


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
    """Twin blow-up of a base graph of degree d-1 via independent-set searches on both sides."""
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
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)
    color = _two_colour(n0, edges0)
    sides = [[v for v in range(n0) if color[v] == c] for c in (0, 1)]
    A_list, B_list = sides[1], sides[0]

    now = time.monotonic()
    total = max(0.0, deadline - now)
    k = d - 1

    # Lines side: blown lines must pairwise share no point. Ideal size |points| / k.
    # Give it a bounded share of time; it exits early when the target is reached.
    S_A = _side(A_list, cs, rng, now + 0.35 * total, len(B_list) // k)
    # Points side: blown points must pairwise share no line. Uses all remaining time.
    S_B = _side(B_list, cs, rng, deadline, len(A_list) // k)
    return _blow(n0, edges0, S_A + S_B)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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
