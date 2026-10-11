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
# two copies (v, v') that share the same neighbourhood. Each copy of u then has
# degree sum_{v in N(u)} m_v = (d-1) + |N(u) ∩ S| where S = {v : m_v = 2}. So S
# must have no two vertices with a common neighbour. Blow-ups keep bipartiteness
# and diameter, so every such S gives a valid graph with n0 + |S| vertices.
#
# The conflict graph never links the two colour classes, so the sides are
# independent subproblems, each solved with its own time slice.
#
# NEW in this version: the independent-set solver is an Andrade-Resende-Werneck
# style iterated local search. It uses (1,2)-swaps (remove one chosen vertex,
# insert two non-adjacent vertices that were blocked only by it) and forced
# perturbations with restarts from the best set. This replaces the old
# min-conflicts search, which stalled well below the best partial ovoid.
# ----------------------------------------------------------------------------

def _mis_ils(N, nb, rng, deadline):
    """Iterated local search for a large independent set in the conflict graph nb."""
    if N == 0:
        return []
    nbs = [set(x) for x in nb]
    inS = [False] * N
    tight = [0] * N          # number of chosen neighbours of each vertex
    sol = set()

    def ins(v):
        inS[v] = True
        sol.add(v)
        for u in nb[v]:
            tight[u] += 1

    def rem(v):
        inS[v] = False
        sol.discard(v)
        for u in nb[v]:
            tight[u] -= 1

    def fill():
        free = [v for v in range(N) if not inS[v] and tight[v] == 0]
        rng.shuffle(free)
        for v in free:
            if not inS[v] and tight[v] == 0:
                ins(v)

    def local_search():
        improved = True
        while improved:
            improved = False
            fill()
            xs = list(sol)
            rng.shuffle(xs)
            for x in xs:
                if not inS[x]:
                    continue
                cand = [u for u in nb[x] if tight[u] == 1]
                if len(cand) < 2:
                    continue
                rng.shuffle(cand)
                pair = None
                for i in range(len(cand)):
                    u = cand[i]
                    for j in range(i + 1, len(cand)):
                        w = cand[j]
                        if w not in nbs[u]:
                            pair = (u, w)
                            break
                    if pair is not None:
                        break
                if pair is not None:
                    rem(x)
                    ins(pair[0])
                    ins(pair[1])
                    improved = True
                    break

    local_search()
    best = list(sol)
    it = 0
    while time.monotonic() < deadline:
        it += 1
        v = rng.randrange(N)
        if inS[v]:
            continue
        # Forced insertion: drop chosen neighbours of v, add v, then repair.
        for u in nb[v]:
            if inS[u]:
                rem(u)
        ins(v)
        local_search()
        if len(sol) > len(best):
            best = list(sol)
        elif len(sol) + 1 < len(best):
            # Too far below the incumbent: restart from the best set.
            for u in list(sol):
                rem(u)
            for u in best:
                ins(u)
    return best


def _sides(n0, adj):
    """Two-colour the base graph (it is bipartite); return the two colour classes."""
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
    classes = [[], []]
    for v in range(n0):
        classes[max(color[v], 0)].append(v)
    return classes


def _solve_side(side, nb, rng, deadline):
    """Maximum-ish conflict-free subset of one colour class (conflicts stay inside the class)."""
    loc = {v: i for i, v in enumerate(side)}
    lnb = [[loc[w] for w in nb[v] if w in loc] for v in side]
    sol = _mis_ils(len(side), lnb, rng, deadline)
    return [side[i] for i in sol]


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

    sides = _sides(n0, adj)
    S = []
    now = time.monotonic()
    span = max(0.0, deadline - now)
    k = len(sides)
    for idx, side in enumerate(sides):
        if not side:
            continue
        sub_deadline = now + span * (idx + 1) / k
        S.extend(_solve_side(side, nb, rng, sub_deadline))
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.87 * time_limit - 3.5)
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
        try:
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
        except Exception:
            # Any failure in the search keeps the best verified graph so far.
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
