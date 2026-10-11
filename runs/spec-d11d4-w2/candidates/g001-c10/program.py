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
# of base degree d-1 gains one degree for each blown neighbour, so it may have
# at most one blown neighbour. So we need, on each side of the bipartition, an
# independent set in the "share a neighbour" conflict graph:
#   - side A: a partial spread (pairwise disjoint neighbourhoods);
#   - side B: a partial ovoid (no two sharing a neighbour).
# Both are maximum-independent-set problems, solved here by an
# ARW-style (1,2)-swap local search with perturbation and restarts from best.
# ----------------------------------------------------------------------------

def _mis(N, adj, rng, deadline):
    """Large independent set in the graph on 0..N-1 with symmetric adjacency lists adj."""
    if N == 0:
        return []
    adjs = [set(a) for a in adj]
    inS = [False] * N
    tight = [0] * N            # number of solution neighbours of each vertex
    sol = set()

    def ins(v):
        inS[v] = True
        sol.add(v)
        for u in adj[v]:
            tight[u] += 1

    def rem(v):
        inS[v] = False
        sol.discard(v)
        for u in adj[v]:
            tight[u] -= 1

    def fill():
        free = [v for v in range(N) if not inS[v] and tight[v] == 0]
        rng.shuffle(free)
        for v in free:
            if not inS[v] and tight[v] == 0:
                ins(v)

    def two_improve():
        improved = True
        while improved:
            improved = False
            xs = list(sol)
            rng.shuffle(xs)
            for x in xs:
                if not inS[x]:
                    continue
                # Neighbours whose only solution neighbour is x.
                cand = [u for u in adj[x] if not inS[u] and tight[u] == 1]
                if len(cand) < 2:
                    continue
                rng.shuffle(cand)
                done = False
                for i in range(len(cand)):
                    u = cand[i]
                    for j in range(i + 1, len(cand)):
                        w = cand[j]
                        if w not in adjs[u]:
                            rem(x)
                            ins(u)
                            ins(w)
                            fill()
                            done = True
                            break
                    if done:
                        break
                if done:
                    improved = True

    fill()
    two_improve()
    best = list(sol)
    best_size = len(best)

    while time.monotonic() < deadline and best_size < N:
        # Perturbation: force in a poorly-constrained outside vertex.
        cands = []
        for _ in range(4):
            v = rng.randrange(N)
            if not inS[v]:
                cands.append(v)
        if not cands:
            continue
        v = min(cands, key=lambda x: tight[x])
        for u in adj[v]:
            if inS[u]:
                rem(u)
        ins(v)
        fill()
        two_improve()

        if len(sol) > best_size:
            best = list(sol)
            best_size = len(best)
        elif len(sol) < best_size - 2 and rng.random() < 0.2:
            # Restart from the best solution found so far.
            inS[:] = [False] * N
            tight[:] = [0] * N
            sol.clear()
            for x in best:
                ins(x)
    return best


def _side_search(V, cs, rng, deadline):
    """Large conflict-free subset of one side V, using conflict lists cs."""
    idx = {v: i for i, v in enumerate(V)}
    adj = [[idx[w] for w in cs[v] if w in idx] for v in V]
    res = _mis(len(V), adj, rng, deadline)
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
    """Twin blow-up of a base graph of degree d-1, using MIS searches on both sides."""
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

    now = time.monotonic()
    total = max(0.0, deadline - now)

    # Side 1: partial spread, half the time.
    S = _side_search(sides[1], cs, rng, now + 0.5 * total)
    # Side 0: partial ovoid, the remaining time.
    S += _side_search(sides[0], cs, rng, deadline)
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
