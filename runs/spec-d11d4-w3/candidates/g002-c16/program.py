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
# Exact symplectic spread of W(q) built from F_{q^2}^2.
# ----------------------------------------------------------------------------

def _symplectic_quadrangle(q):
    """Return (npts, lines, spread) for W(q) built from F_{q^2}^2, or None."""
    Q = q * q
    F = lib.GF(Q)
    mul, add, sub = F.mul, F.add, F.sub
    subfield = [x for x in range(Q) if F.pow(x, q) == x]
    if len(subfield) != q:
        return None
    scal = [x for x in subfield if x]
    tr = [add(z, F.pow(z, q)) for z in range(Q)]
    delta = 1

    pid = [-1] * (Q * Q)
    reps = []
    for a in range(Q):
        for b in range(Q):
            if (a or b) and pid[a * Q + b] < 0:
                k = len(reps)
                reps.append((a, b))
                for l in scal:
                    pid[mul(l, a) * Q + mul(l, b)] = k
    npts = len(reps)
    if npts != (Q * Q - 1) // (q - 1):
        return None

    def collinear(x, y):
        det = sub(mul(x[0], y[1]), mul(x[1], y[0]))
        return tr[mul(delta, det)] == 0

    covered = [set() for _ in range(npts)]
    lines = []
    for i in range(npts):
        x = reps[i]
        for j in range(i + 1, npts):
            if j in covered[i]:
                continue
            y = reps[j]
            if not collinear(x, y):
                continue
            L = set()
            for a in subfield:
                ax0, ax1 = mul(a, x[0]), mul(a, x[1])
                for b in subfield:
                    if a == 0 and b == 0:
                        continue
                    v0 = add(ax0, mul(b, y[0]))
                    v1 = add(ax1, mul(b, y[1]))
                    L.add(pid[v0 * Q + v1])
            if len(L) != q + 1:
                return None
            for p in L:
                covered[p] |= L
            lines.append(sorted(L))

    pdeg = [0] * npts
    for L in lines:
        for p in L:
            pdeg[p] += 1
    if any(c != q + 1 for c in pdeg):
        return None

    line_idx = {frozenset(L): j for j, L in enumerate(lines)}
    spread = []
    for v0, v1 in [(1, t) for t in range(Q)] + [(0, 1)]:
        key = frozenset(pid[mul(l, v0) * Q + mul(l, v1)] for l in range(1, Q))
        j = line_idx.get(key)
        if j is None:
            return None
        spread.append(j)
    if len(set(spread)) != Q + 1:
        return None
    return npts, lines, spread


# ----------------------------------------------------------------------------
# NEW: (1,2)-swap iterated local search for maximum independent set.
#
# Maintains an independent set S and, for every vertex, the number of its
# neighbours in S ("tightness"). Improvements are:
#   * free insertion: a vertex with tightness 0 joins S;
#   * (1,2)-swap: a vertex x in S is replaced by two non-adjacent vertices whose
#     only S-neighbour is x (ARW-style).
# Perturbation forces a low-tightness outside vertex into S, then re-optimises.
# This replaces the older tabu search, which stalled far below the optimum.
# ----------------------------------------------------------------------------

def _mis_ils(N, nbr, rng, deadline):
    """Return a large independent set of the graph (N vertices, adjacency lists nbr)."""
    if N == 0:
        return []
    nbs = [set(a) for a in nbr]
    inS = [False] * N
    tight = [0] * N
    sz = [0]

    def add(v):
        inS[v] = True
        sz[0] += 1
        for u in nbr[v]:
            tight[u] += 1

    def rem(v):
        inS[v] = False
        sz[0] -= 1
        for u in nbr[v]:
            tight[u] -= 1

    def fill():
        order = list(range(N))
        rng.shuffle(order)
        for v in order:
            if not inS[v] and tight[v] == 0:
                add(v)

    def improve():
        while True:
            sol = [v for v in range(N) if inS[v]]
            rng.shuffle(sol)
            changed = False
            for x in sol:
                if not inS[x]:
                    continue
                cand = [u for u in nbr[x] if tight[u] == 1]
                if len(cand) < 2:
                    continue
                pair = None
                for i in range(len(cand)):
                    u = cand[i]
                    nu = nbs[u]
                    for j in range(i + 1, len(cand)):
                        w = cand[j]
                        if w not in nu:
                            pair = (u, w)
                            break
                    if pair:
                        break
                if pair:
                    rem(x)
                    add(pair[0])
                    add(pair[1])
                    fill()
                    changed = True
            if not changed:
                break

    def load(sol):
        for v in range(N):
            inS[v] = False
            tight[v] = 0
        sz[0] = 0
        for v in sol:
            add(v)

    fill()
    improve()
    best = [v for v in range(N) if inS[v]]
    best_size = len(best)

    while time.monotonic() < deadline:
        # Perturbation: pick the least-tight outside vertex from a small sample.
        v = -1
        bt = 10 ** 9
        for _ in range(12):
            c = rng.randrange(N)
            if not inS[c] and tight[c] < bt:
                v, bt = c, tight[c]
        if v < 0:
            continue
        for u in nbr[v]:
            if inS[u]:
                rem(u)
        add(v)
        fill()
        improve()
        if sz[0] > best_size:
            best = [w for w in range(N) if inS[w]]
            best_size = len(best)
        elif sz[0] < best_size - 2 or (sz[0] < best_size and rng.random() < 0.05):
            load(best)
    return best


def _ovoid_search(npts, lines, rng, nprng, deadline):
    """Large partial ovoid of the points: pairwise non-collinear point set."""
    nb = [set() for _ in range(npts)]
    for L in lines:
        for p in L:
            nb[p].update(L)
    nbl = []
    for p in range(npts):
        s = nb[p]
        s.discard(p)
        nbl.append(sorted(s))
    return _mis_ils(npts, nbl, rng, deadline)


def _side_search(V, cs, rng, nprng, deadline):
    """Large conflict-free subset of one side V, using local conflict lists cs."""
    idx = {v: i for i, v in enumerate(V)}
    nb_local = [[idx[w] for w in cs[v] if w in idx] for v in V]
    res = _mis_ils(len(V), nb_local, rng, deadline)
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


def _blowup(n0, edges0, d, deadline, rng, nprng):
    """Twin blow-up of a base graph of degree d-1, searching each side separately."""
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
    S = []
    S += _side_search(sides[0], cs, rng, nprng, now + 0.5 * total)
    S += _side_search(sides[1], cs, rng, nprng, deadline)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.88 * time_limit - 3.0)
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

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

    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        done = False
        if D >= 4:
            try:
                geo = _symplectic_quadrangle(q)
                if geo is not None:
                    npts, lines, spread = geo
                    n0 = npts + len(lines)
                    edges0 = [(p, npts + j) for j, L in enumerate(lines) for p in L]
                    consider(n0, edges0)
                    O = _ovoid_search(npts, lines, rng, nprng, deadline)
                    S = list(O) + [npts + j for j in spread]
                    n, e = _blow(n0, edges0, S)
                    consider(n, e)
                    done = True
            except Exception:
                done = False

        if not done:
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
