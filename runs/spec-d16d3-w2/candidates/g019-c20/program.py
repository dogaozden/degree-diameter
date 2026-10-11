import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), as in the parent.
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each point P in an
# arc S gets a new X-vertex joined to the lines through P, and each line j in S gets
# a new Y-vertex joined to the points on j. Then X-X and Y-Y pairs are covered and
# the graph has diameter 3. Saturation adds spare X-Y edges.
#
# NEW IDEA: two-sided covering growth.
# For a bipartite graph with parts X and Y, diameter 3 is implied by:
#   (a) every two X-vertices have a common neighbour, and
#   (b) every two Y-vertices have a common neighbour.
# (Given (a) and (b), any non-adjacent x, y satisfy x - y' - x' - y with
# x' in N(y), which has length 3.) Starting from a valid balanced biregular
# graph, grow by one X-vertex and one Y-vertex of degree d. Their edges come from
# removing d disjoint edges and rewiring. Then simulated annealing repairs
# uncovered pairs with degree-preserving "edge exchanges" aimed at a chosen
# uncovered pair. Incremental matrix updates keep each step cheap.
# ----------------------------------------------------------------------------


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new X-vertex per point of S and a new Y-vertex per line of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _saturate(n, edges, m, k, d, rng):
    """Add every missing X-Y edge while both endpoints have spare degree < d."""
    E = set()
    for u, v in edges:
        E.add((u, v) if u < v else (v, u))
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    X = [v for v in range(n) if v < m or 2 * m <= v < 2 * m + k]
    Y = [v for v in range(n) if m <= v < 2 * m or v >= 2 * m + k]
    spare_x = [v for v in X if deg[v] < d]
    spare_y = [v for v in Y if deg[v] < d]
    pairs = [(x, y) for x in spare_x for y in spare_y]
    rng.shuffle(pairs)
    for x, y in pairs:
        if deg[x] >= d or deg[y] >= d:
            continue
        key = (x, y) if x < y else (y, x)
        if key in E:
            continue
        E.add(key)
        deg[x] += 1
        deg[y] += 1
    return n, sorted(E)


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, S)
        n_c, e_c = _saturate(n_c, e_c, m, len(S), d, rng)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Two-sided covering growth (new in this version).
# ----------------------------------------------------------------------------

def _biadjacency(n, edges):
    """Return a square 0/1 float32 matrix C with X = colour-0 vertices, Y = colour-1, or None."""
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    if n == 0:
        return None
    color[0] = 0
    stack = [0]
    while stack:
        u = stack.pop()
        for v in adj[u]:
            if color[v] == -1:
                color[v] = 1 - color[u]
                stack.append(v)
            elif color[v] == color[u]:
                return None
    if any(c < 0 for c in color):
        return None
    X = [v for v in range(n) if color[v] == 0]
    Y = [v for v in range(n) if color[v] == 1]
    if len(X) != len(Y):
        return None
    ix = {v: i for i, v in enumerate(X)}
    iy = {v: j for j, v in enumerate(Y)}
    C = np.zeros((len(X), len(Y)), dtype=np.float32)
    for u, v in edges:
        if color[u] == 0:
            C[ix[u], iy[v]] = 1.0
        else:
            C[ix[v], iy[u]] = 1.0
    return C


def _to_graph(C):
    """Biadjacency matrix -> (n, edges) with X = 0..N-1 and Y = N..2N-1."""
    N = C.shape[0]
    edges = [(int(i), N + int(j)) for i, j in np.argwhere(C > 0)]
    return 2 * N, edges


def _uncovered(MX, MY):
    """Ordered lists of uncovered same-side pairs (diagonal excluded)."""
    np.fill_diagonal(MX, 1.0)
    np.fill_diagonal(MY, 1.0)
    return np.argwhere(MX == 0), np.argwhere(MY == 0)


def _apply(M, MX, MY, r, c, delta):
    """Change M[r, c] by delta and keep MX = M M^T, MY = M^T M exact off the diagonal."""
    col = M[:, c].copy()
    row = M[r, :].copy()
    MX[r, :] += delta * col
    MX[:, r] += delta * col
    MY[c, :] += delta * row
    MY[:, c] += delta * row
    M[r, c] += delta


def _grow_one(C, d, rng, deadline):
    """Add one X-vertex and one Y-vertex (both degree d) and repair coverage by annealing.

    Returns the new (N+1)x(N+1) matrix, or None if no fully covered graph was found in time.
    """
    N = C.shape[0]
    ed = np.argwhere(C > 0)
    if len(ed) < d:
        return None
    order = list(range(len(ed)))
    rng.shuffle(order)
    usedx, usedy, picked = set(), set(), []
    for idx in order:
        a = int(ed[idx, 0])
        b = int(ed[idx, 1])
        if a in usedx or b in usedy:
            continue
        usedx.add(a)
        usedy.add(b)
        picked.append((a, b))
        if len(picked) == d:
            break
    if len(picked) < d:
        return None

    # New x = N joins the b_i, new y = N joins the a_i, removing the matched edges (a_i, b_i).
    M = np.zeros((N + 1, N + 1), dtype=np.float32)
    M[:N, :N] = C
    for a, b in picked:
        M[a, b] = 0.0
        M[a, N] = 1.0
        M[N, b] = 1.0

    MX = np.ascontiguousarray(M @ M.T)
    MY = np.ascontiguousarray(M.T @ M)
    ux, uy = _uncovered(MX, MY)
    cost = (len(ux) + len(uy)) // 2
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = 1.0

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 1.0 * (0.12 ** min(1.0, (now - t0) / span))
        nx_ = len(ux)
        total = nx_ + len(uy)
        r = rng.randrange(total)
        # Targeted move: make an uncovered same-side pair share a neighbour.
        if r < nx_:
            a, b = int(ux[r, 0]), int(ux[r, 1])
            cand = np.flatnonzero((M[b] > 0) & (M[a] == 0))
            if len(cand) == 0:
                continue
            x = a
            y = int(cand[rng.randrange(len(cand))])
        else:
            a, b = int(uy[r - nx_, 0]), int(uy[r - nx_, 1])
            cand = np.flatnonzero((M[:, b] > 0) & (M[:, a] == 0))
            if len(cand) == 0:
                continue
            x = int(cand[rng.randrange(len(cand))])
            y = a
        # Add (x, y); remove (x, y1) and (x2, y); add (x2, y1). All degrees are preserved.
        Nx = np.flatnonzero(M[x] > 0)
        Ny = np.flatnonzero(M[:, y] > 0)
        if len(Nx) == 0 or len(Ny) == 0:
            continue
        y1 = int(Nx[rng.randrange(len(Nx))])
        x2 = int(Ny[rng.randrange(len(Ny))])
        if M[x2, y1] > 0:
            continue
        _apply(M, MX, MY, x, y, 1.0)
        _apply(M, MX, MY, x, y1, -1.0)
        _apply(M, MX, MY, x2, y, -1.0)
        _apply(M, MX, MY, x2, y1, 1.0)
        ux2, uy2 = _uncovered(MX, MY)
        c2 = (len(ux2) + len(uy2)) // 2
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            ux, uy, cost = ux2, uy2, c2
        else:
            _apply(M, MX, MY, x, y, -1.0)
            _apply(M, MX, MY, x, y1, 1.0)
            _apply(M, MX, MY, x2, y, 1.0)
            _apply(M, MX, MY, x2, y1, -1.0)

    return M if cost == 0 else None


def _grow(C, d, rng, deadline, consider):
    """Repeatedly grow the balanced graph by one vertex per side while time allows."""
    while True:
        remain = deadline - time.monotonic()
        if remain < 0.5:
            break
        attempt = time.monotonic() + max(2.0, 0.6 * remain)
        C2 = _grow_one(C, d, rng, min(deadline, attempt))
        if C2 is None:
            continue
        C = C2
        n, e = _to_graph(C)
        consider(n, e)
    return C


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4), kept from the parent.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Annealed group voltage lifts for D >= 4, kept from the parent.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is d-regular.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Arc-extended projective plane graphs (diameter 3, valid for all D >= 3).
    arcs = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
    arcs.sort(key=lambda t: -t[0])
    for n_c, e_c in arcs:
        if n_c > best_n:
            consider(n_c, e_c)

    if D == 3:
        # Grow the best balanced graph by covering-repair annealing.
        # Skip when already at the Moore bound (e.g. d = 3, D = 3 gives the Heawood graph).
        if best_n < lib.moore_bound(d, D) and time.monotonic() < deadline:
            C0 = _biadjacency(best[0], best[1])
            if C0 is not None:
                _grow(C0, d, rng, deadline, consider)
    else:
        if time.monotonic() < deadline:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        ks = [1, 2, 2, 3, 4]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
