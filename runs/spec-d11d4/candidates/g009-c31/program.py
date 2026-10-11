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
# If every vertex of a base graph G has degree d-1, blow up some vertices v into
# two twin copies with the same neighbourhood. Blown-up vertices on the same
# side must have no common neighbour. For W(q) this means a partial ovoid on
# points (pairwise non-collinear) and a partial spread on lines.
# ----------------------------------------------------------------------------

def _mis(N, adj, rng, deadline, target):
    """Iterated local search for a large independent set (ARW-style).

    Moves:
      * free insertion (vertex with no solution neighbour),
      * (1,2)-swap: remove x and insert two non-adjacent vertices whose only
        solution neighbour is x,
      * perturbation: force-insert a low-tightness outside vertex, then
        re-optimise; fall back to the best solution if the walk drifts too far.
    Stops early once the size reaches `target`.
    """
    if N == 0:
        return []
    aset = [set(a) for a in adj]
    inS = [False] * N
    tau = [0] * N
    sol = []
    pos = [-1] * N

    def add(v):
        inS[v] = True
        pos[v] = len(sol)
        sol.append(v)
        for u in adj[v]:
            tau[u] += 1

    def rem(v):
        inS[v] = False
        i = pos[v]
        last = sol[-1]
        sol[i] = last
        pos[last] = i
        sol.pop()
        pos[v] = -1
        for u in adj[v]:
            tau[u] -= 1

    def local_search():
        improved = True
        while improved:
            improved = False
            for v in range(N):
                if not inS[v] and tau[v] == 0:
                    add(v)
                    improved = True
            cand = list(sol)
            rng.shuffle(cand)
            for x in cand:
                if not inS[x]:
                    continue
                L = [u for u in adj[x] if not inS[u] and tau[u] == 1]
                if len(L) < 2:
                    continue
                done = False
                for i in range(len(L)):
                    a = L[i]
                    sa = aset[a]
                    for j in range(i + 1, len(L)):
                        b = L[j]
                        if b not in sa:
                            rem(x)
                            add(a)
                            add(b)
                            done = True
                            break
                    if done:
                        break
                if done:
                    improved = True

    order = list(range(N))
    rng.shuffle(order)
    for v in order:
        if not inS[v] and tau[v] == 0:
            add(v)
    local_search()
    best = list(sol)
    best_size = len(sol)

    while best_size < target and time.monotonic() < deadline:
        pool = [v for v in range(N) if not inS[v] and tau[v] <= 2]
        if not pool:
            pool = [v for v in range(N) if not inS[v]]
        if not pool:
            break
        v = pool[rng.randrange(len(pool))]
        for u in adj[v]:
            if inS[u]:
                rem(u)
        add(v)
        local_search()
        if len(sol) > best_size:
            best_size = len(sol)
            best = list(sol)
        elif len(sol) < best_size - 1:
            for u in list(sol):
                rem(u)
            for u in best:
                add(u)
    return best


def _side_search(V, cs, rng, deadline, target):
    """Large conflict-free subset of one side V, using conflict sets cs."""
    idx = {v: i for i, v in enumerate(V)}
    adj = [[idx[w] for w in cs[v] if w in idx] for v in V]
    res = _mis(len(V), adj, rng, deadline, target)
    return [V[i] for i in res]


def _two_colour(n, edges):
    """Return a 0/1 colouring of a bipartite graph (each component starts at 0)."""
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


def _blowup(n0, edges0, d, q, deadline, rng):
    """Twin blow-up of a base graph of degree d-1 (W(q): points = colour 0, lines = colour 1)."""
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
    # Spread side (lines) has a hard bound q^2+1 and is searched first, with
    # early stop; any time it saves goes to the ovoid side (points).
    tgt_lines = q * q + 1
    tgt_pts = q * q + 1 if q % 2 == 0 else q * q - q + 1  # Tallini bound for q odd
    S = []
    S += _side_search(sides[1], cs, rng, now + 0.5 * total, tgt_lines)
    S += _side_search(sides[0], cs, rng, deadline, tgt_pts)
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
            res = _blowup(n0, e0, d, q, deadline, rng)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
