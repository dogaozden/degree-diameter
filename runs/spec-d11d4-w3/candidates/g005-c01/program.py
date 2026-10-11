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
# two copies (v, v') sharing the same neighbourhood. A copy of u then has degree
# (d-1) + |N(u) ∩ S| with S the doubled set, so S must contain no two vertices
# with a common neighbour. Those conflicts stay inside one colour class, so the
# two sides are solved independently.
#
# NEW in this version:
#   * Packing view. For a side X, the rows are the neighbourhoods N(x), x in X,
#     and a conflict-free set is a family of pairwise disjoint rows. A randomised
#     exact-cover-style DFS (min-remaining-options branching, with restarts)
#     searches for large disjoint families. On W(q) the line side has a full
#     spread (q^2+1 lines) and the DFS can find it, which is the optimum there.
#   * Independent-set ILS. The DFS result seeds an iterated local search with
#     (1,2)-swaps and random forced insertions. It keeps the best solution and
#     restores it when a perturbation loses ground.
# ----------------------------------------------------------------------------

def _dlx_packing(rows, m, rng, deadline, target):
    """Largest family of pairwise disjoint rows found by randomised restarted DFS.

    rows[r] lists the elements (0..m-1) of row r. Returns a list of row indices.
    """
    R = len(rows)
    col = [[] for _ in range(m)]
    for r, els in enumerate(rows):
        for e in els:
            col[e].append(r)
    best = []
    per_try = 200
    while time.monotonic() < deadline and len(best) < target:
        covered = [False] * m
        blocked = [0] * R
        chosen = []
        nodes = [0]
        stop = [False]

        def cover(r, s):
            for e in rows[r]:
                covered[e] = s > 0
                for r2 in col[e]:
                    blocked[r2] += s

        def dfs():
            nonlocal best
            if len(chosen) > len(best):
                best = list(chosen)
                if len(best) >= target:
                    stop[0] = True
                    return
            nodes[0] += 1
            if nodes[0] > per_try or time.monotonic() > deadline:
                stop[0] = True
                return
            bestOpts = None
            for e in range(m):
                if covered[e]:
                    continue
                opts = [r for r in col[e] if blocked[r] == 0]
                if bestOpts is None or len(opts) < len(bestOpts):
                    bestOpts = opts
                    if not opts:
                        break
            if bestOpts is None or not bestOpts:
                return
            rng.shuffle(bestOpts)
            for r in bestOpts:
                cover(r, 1)
                chosen.append(r)
                dfs()
                chosen.pop()
                cover(r, -1)
                if stop[0]:
                    return

        dfs()
    return best


def _ils(N, nbs, rng, deadline, init):
    """Iterated local search for a large independent set (no conflicting pair).

    nbs[i] lists the conflict-neighbours of i. Uses (1,2)-swaps, random forced
    insertions and restoration of the best solution when the search loses ground.
    """
    if N == 0:
        return []
    adjs = [set(x) for x in nbs]
    insol = [False] * N
    tight = [0] * N
    sol = set()

    def ins(v):
        insol[v] = True
        sol.add(v)
        for u in nbs[v]:
            tight[u] += 1

    def rem(v):
        insol[v] = False
        sol.discard(v)
        for u in nbs[v]:
            tight[u] -= 1

    def fill(cands):
        for u in cands:
            if not insol[u] and tight[u] == 0:
                ins(u)

    def local_search():
        improved = True
        while improved:
            improved = False
            for x in list(sol):
                cand = [u for u in nbs[x] if not insol[u] and tight[u] == 1]
                if len(cand) < 2:
                    continue
                pair = None
                for i in range(len(cand)):
                    ai = adjs[cand[i]]
                    for j in range(i + 1, len(cand)):
                        if cand[j] not in ai:
                            pair = (cand[i], cand[j])
                            break
                    if pair:
                        break
                if pair:
                    rem(x)
                    ins(pair[0])
                    ins(pair[1])
                    fill(nbs[x])
                    improved = True
                    break

    def restore():
        for v in list(sol):
            rem(v)
        for v in best:
            ins(v)

    fill(init)
    order = list(range(N))
    rng.shuffle(order)
    fill(order)
    local_search()
    best = list(sol)
    while len(best) < N and time.monotonic() < deadline:
        v = rng.randrange(N)
        if not insol[v]:
            removed = [u for u in nbs[v] if insol[u]]
            for u in removed:
                rem(u)
            ins(v)
            for u in removed:
                fill(nbs[u])
        local_search()
        if len(sol) > len(best):
            best = list(sol)
        elif len(sol) < len(best):
            restore()
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


def _solve_side(side, other, adj, nb, rng, deadline):
    """Conflict-free subset of one colour class; conflicts stay inside the class."""
    loc = {v: i for i, v in enumerate(side)}
    oloc = {v: i for i, v in enumerate(other)}
    lnb = [[loc[w] for w in nb[v] if w in loc] for v in side]
    rows = [[oloc[u] for u in adj[v]] for v in side]
    m = len(other)
    now = time.monotonic()
    init = []
    if rows and m and all(rows):
        target = m // min(len(r) for r in rows)
        init = _dlx_packing(rows, m, rng, now + 0.3 * max(0.0, deadline - now), target)
    sol = _ils(len(side), lnb, rng, deadline, init)
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
                cs[a[i]].add(a[j])
                cs[a[j]].add(a[i])
    nb = [sorted(s) for s in cs]
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)

    sides = _sides(n0, adj)
    now = time.monotonic()
    span = max(0.0, deadline - now)
    k = len(sides)
    S = []
    for idx, side in enumerate(sides):
        if not side:
            continue
        other = sides[1 - idx]
        sub_deadline = now + span * (idx + 1) / k
        S.extend(_solve_side(side, other, adj, nb, rng, sub_deadline))
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 3.0)
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
