import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000
GQ_Q_MAX = 9
ARC_Q_MAX = 23
S_LIST = (1, 2, 3, 4, 5, 6)
RETRIES = 2
ITERS_CYC = 6000
ITERS_GROUP = 600
POST_LIFTS = 3
_BIG = 10 ** 9


# ---------------------------------------------------------------- shared helpers

def _two_colour(n, edges):
    """Proper 2-colouring of a bipartite graph, component by component."""
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
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
    return color


def _best_valid(cands, d, D):
    """Largest candidate passing lib.is_valid, or None."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return None


def _finish(pool, d, D, fallback):
    bv = _best_valid(pool, d, D)
    return bv if bv is not None else fallback


def _greedy_cover(cand, sets, target, budget):
    """Pick at most `budget` candidates whose bitmasks cover `target`; None if impossible."""
    cand = list(cand)
    covered = 0
    chosen = []
    while (target & ~covered) and len(chosen) < budget and cand:
        best_u, best_gain = -1, 0
        for u in cand:
            g = (sets[u] & target & ~covered).bit_count()
            if g > best_gain:
                best_u, best_gain = u, g
        if best_u < 0:
            break
        chosen.append(best_u)
        covered |= sets[best_u]
        cand.remove(best_u)
    if target & ~covered:
        return None
    return chosen


# ---------------------------------------------------------------- growth (add vertices)

def _extend(n, edges, d, D, rng, deadline):
    """Greedily add single vertices attached to a set cover of the current graph."""
    edges = list(edges)
    if D < 2 or n == 0:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    full = (1 << n) - 1
    while time.monotonic() < deadline:
        balls = lib._balls(n, edges, D - 1)
        grown = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            cand = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            rng.shuffle(cand)
            chosen = _greedy_cover(cand, balls, full, d)
            if chosen:
                x = n
                n += 1
                color.append(c)
                deg.append(len(chosen))
                for u in chosen:
                    edges.append((u, x))
                    deg[u] += 1
                full = (1 << n) - 1
                grown = True
                break
        if not grown:
            break
    return n, edges


def _pair_extend(n, edges, d, D, rng, deadline):
    """Add two adjacent new vertices at once."""
    edges = list(edges)
    if D < 3 or n == 0 or d < 2:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    full = (1 << n) - 1
    while time.monotonic() < deadline:
        b1 = lib._balls(n, edges, D - 1)
        b2 = lib._balls(n, edges, D - 2)
        placed = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            side_other = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            side_c = [u for u in range(n) if color[u] == c and deg[u] < d]
            N = _greedy_cover(side_other, b1, full, d - 1)
            if not N:
                continue
            b2N = 0
            for u in N:
                b2N |= b2[u]
            M = _greedy_cover(side_c, b1, full & ~b2N, d - 1)
            if M is None:
                continue
            x, y = n, n + 1
            n += 2
            color.append(c)
            color.append(1 - c)
            deg.append(len(N) + 1)
            deg.append(len(M) + 1)
            for u in N:
                edges.append((u, x))
                deg[u] += 1
            for u in M:
                edges.append((u, y))
                deg[u] += 1
            edges.append((x, y))
            full = (1 << n) - 1
            placed = True
            break
        if not placed:
            break
    return n, edges


def _grow(n, edges, d, D, rng, deadline):
    """Alternate single and paired greedy extension until neither adds anything."""
    prev = -1
    while n != prev and time.monotonic() < deadline:
        prev = n
        n, edges = _extend(n, edges, d, D, rng, deadline)
        n, edges = _pair_extend(n, edges, d, D, rng, deadline)
    return n, edges


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree."""
    rng = random.Random(seed + 7)
    color = _two_colour(n, edges)
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    side0 = [u for u in range(n) if color[u] == 0]
    side1 = [v for v in range(n) if color[v] == 1]
    new_edges = list(edges)
    for _ in range(3):
        us = [u for u in side0 if deg[u] < d]
        rng.shuffle(us)
        for u in us:
            if deg[u] >= d:
                continue
            cands = [v for v in side1 if deg[v] < d and v not in adj[u]]
            if not cands:
                continue
            v = rng.choice(cands)
            adj[u].add(v)
            adj[v].add(u)
            deg[u] += 1
            deg[v] += 1
            new_edges.append((u, v))
    return n, new_edges


# ---------------------------------------------------------------- iterated remove-and-regrow

def _remove_vertex(n, edges, v):
    out = []
    for a, b in edges:
        if a == v or b == v:
            continue
        out.append((a - 1 if a > v else a, b - 1 if b > v else b))
    return n - 1, out


def _ils(n, edges, d, D, rng, end):
    """Delete a random vertex, regrow, accept if valid and not too small."""
    cur = (n, list(edges))
    best = cur
    while time.monotonic() < end:
        n0, e0 = cur
        if n0 < 4:
            break
        v = rng.randrange(n0)
        m, e1 = _remove_vertex(n0, e0, v)
        m, e2 = _grow(m, e1, d, D, rng, min(end, time.monotonic() + 0.3))
        if m < best[0] - 2:
            continue
        accept = m >= n0 or (m == n0 - 1 and rng.random() < 0.2)
        if accept and lib.is_valid(m, e2, d, D):
            cur = (m, e2)
            if m > best[0]:
                best = (m, e2)
    return best


# ---------------------------------------------------------------- D = 3 : arc-extended projective planes

def _pg_data(q):
    """Incidence data for PG(2, q): points and lines share indices 0..m-1."""
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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A-vertex per S-point and a new B-vertex per S-line."""
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


def _arc_candidates(d, deadline, rng):
    """For each prime power q <= d-1, an arc-extended PG(2,q) using spare degree. Diameter 3."""
    out = []
    for q in range(2, min(d - 1, ARC_Q_MAX) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)
        S = []
        if s >= 1:
            S = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if len(cs) > len(S) and _loads_ok(cs, s, m, point_lines, line_points):
                S = cs
        if not _loads_ok(S, s, m, point_lines, line_points):
            S = []
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ---------------------------------------------------------------- D = 3 : polarity double cover

def _polarity_cover(q):
    """Bipartite double cover of the Erdos-Renyi polarity graph ER_q."""
    F = lib.GF(q)
    pts = np.array(lib.projective_points(q), dtype=np.int64)
    m = len(pts)
    mul, add = F.mul_table, F.add_table
    terms = [mul[pts[:, None, c], pts[None, :, c]] for c in range(3)]
    dot = add[add[terms[0], terms[1]], terms[2]]
    A = (dot == 0)
    np.fill_diagonal(A, False)
    rows, cols = np.nonzero(np.triu(A, 1))
    edges = []
    for i, j in zip(rows.tolist(), cols.tolist()):
        edges.append((i, m + j))
        edges.append((j, m + i))
    return 2 * m, edges


def _er_base(d):
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return _polarity_cover(q)


# ---------------------------------------------------------------- D >= 4 : generalized quadrangle

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
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ---------------------------------------------------------------- Haar graphs (hill-climb)

def _search_haar(d, D, m, rng, deadline, iters):
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


# ---------------------------------------------------------------- cyclic lifts (annealing)

def _neighbors(P, Pinv, V, s, m):
    d = P.shape[0]
    g = np.arange(m, dtype=np.int64)
    nbr = np.empty((2 * s * m, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            nbr[i * m:(i + 1) * m, k] = s * m + j * m + (g + int(V[k, i])) % m
        for j in range(s):
            i = int(Pinv[k, j])
            nbr[(s + j) * m:(s + j + 1) * m, k] = i * m + (g - int(V[k, i])) % m
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff valid."""
    n = nbr.shape[0]
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        M = R.copy()
        for k in range(nbr.shape[1]):
            M |= R[:, nbr[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    return int(S * n - np.count_nonzero(R))


def _swap(P, Pinv, k, a, b):
    P[k, a], P[k, b] = P[k, b], P[k, a]
    Pinv[k, P[k, a]] = a
    Pinv[k, P[k, b]] = b


def _anneal_any(s, m, d, D, rng, deadline):
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(m) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * m for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, m)
    cur = _cost(nbr, sources, D)
    for it in range(ITERS_CYC):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS_CYC) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(d), rng.randrange(s)
            old = int(V[k, i])
            new_v = rng.randrange(m)
            if new_v == old:
                continue
            V[k, i] = new_v
            cand = _neighbors(P, Pinv, V, s, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    return cur, P.copy(), V.copy()


def _graph(s, m, P, V, d):
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, m)
    edges = set()
    for x in range(s * m):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * m, sorted(edges)


def _try_size(s, m, d, D, rng, deadline):
    worst = None
    for _ in range(RETRIES):
        if time.monotonic() > deadline:
            break
        cost, P, V = _anneal_any(s, m, d, D, rng, deadline)
        if cost == 0:
            return (P, V), None
        if worst is None or cost < worst[0]:
            worst = (cost, P, V)
    return None, worst


def _search(s, d, D, rng, deadline, cap):
    """For fixed s, find the largest m whose cyclic lift passes annealing."""
    best = None
    lo, hi = 0, None
    m = 1
    while time.monotonic() < deadline:
        if 2 * s * m > cap:
            hi = m
        else:
            st, _miss = _try_size(s, m, d, D, rng, deadline)
            if st is not None:
                lo = m
                best = (m, st[0], st[1])
            else:
                hi = m
        if hi is None:
            m = 2 * lo
        else:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2
    return best


# ---------------------------------------------------------------- semidirect-group lifts

# Group Z_m x|_r Z_k, element (a, b) coded a*k+b, (a,b)(c,d) = (a + r^b c, b + d).
# Left multiplication is an automorphism of the bi-Cayley lift, so BFS from one
# representative per base class decides the diameter for the whole lift.

def _sample_group(G, rng):
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


def _gdart_edges(adj, k, G, i, j, pm, sign):
    """Add (sign>0) or remove (sign<0) the edges of one dart."""
    base_a = i * G
    base_b = (k + j) * G
    for g in range(G):
        a = base_a + g
        b = base_b + pm[g]
        if sign > 0:
            adj[a].append(b)
            adj[b].append(a)
        else:
            adj[a].remove(b)
            adj[b].remove(a)


def _gcost(k, G, D, darts, adj, bound):
    """Pairs (representative, vertex) not within D. Stops early above `bound`."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
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
        if total > bound:
            return total
    return total


def _gedges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _gsearch(k, G, d, D, rng, iters, deadline):
    """Anneal voltages and base-permutation layers in a random semidirect group of order G."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    G = order
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(x, s) for x in range(G)] for _, _, s in darts]
    adj = [[] for _ in range(2 * k * G)]
    for (i, j, _s), pm in zip(darts, perms):
        _gdart_edges(adj, k, G, i, j, pm, 1)
    cost = _gcost(k, G, D, darts, adj, _BIG)

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        accept_anyway = rng.random() < 0.02
        bound = _BIG if accept_anyway else cost
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            i, j, old_s = darts[idx]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_pm = perms[idx]
            new_pm = [mul(x, new_s) for x in range(G)]
            _gdart_edges(adj, k, G, i, j, old_pm, -1)
            _gdart_edges(adj, k, G, i, j, new_pm, 1)
            darts[idx][2] = new_s
            perms[idx] = new_pm
            c2 = _gcost(k, G, D, darts, adj, bound)
            if c2 < _BIG and c2 <= bound:
                cost = c2
            else:
                _gdart_edges(adj, k, G, i, j, new_pm, -1)
                _gdart_edges(adj, k, G, i, j, old_pm, 1)
                darts[idx][2] = old_s
                perms[idx] = old_pm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            ai, aj = darts[ia][0], darts[ia][1]
            bi, bj = darts[ib][0], darts[ib][1]
            pa, pb = perms[ia], perms[ib]
            _gdart_edges(adj, k, G, ai, aj, pa, -1)
            _gdart_edges(adj, k, G, bi, bj, pb, -1)
            _gdart_edges(adj, k, G, ai, bj, pa, 1)
            _gdart_edges(adj, k, G, bi, aj, pb, 1)
            darts[ia][1], darts[ib][1] = bj, aj
            c2 = _gcost(k, G, D, darts, adj, bound)
            if c2 < _BIG and c2 <= bound:
                cost = c2
            else:
                _gdart_edges(adj, k, G, ai, bj, pa, -1)
                _gdart_edges(adj, k, G, bi, aj, pb, -1)
                _gdart_edges(adj, k, G, ai, aj, pa, 1)
                _gdart_edges(adj, k, G, bi, bj, pb, 1)
                darts[ia][1], darts[ib][1] = aj, bj

    if cost == 0:
        return _gedges(k, G, darts, perms)
    return None


def _group_search(d, D, rng, deadline, cap, start_n):
    """Grow the order of group lifts beyond start_n while time remains."""
    best = None
    best_n = start_n
    while time.monotonic() < deadline and best_n < cap:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
        if 2 * k * G > cap:
            G = cap // (2 * k)
            if G < 2:
                break
        res = _gsearch(k, G, d, D, rng, ITERS_GROUP, deadline)
        if res is not None:
            n, edges = res
            if n > best_n and lib.is_valid(n, edges, d, D):
                best_n, best = n, (n, edges)
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    span = max(0.5, 0.8 * time_limit - 1.0)
    end = start + span

    def at(f):
        return start + f * span

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    rng = random.Random(seed * 1000003 + 97 * d + D)
    fallback = lib.haar_graph(d, range(d))
    pool = [fallback]
    cap = min(N_CAP, lib._moore_bound(d, D))
    slice_s = max(0.2, 0.03 * span)

    # Extremal shortcuts (Moore-optimal constructions).
    if D == 3 and lib.is_prime_power(d - 1):
        pool.append(lib.projective_plane_incidence(d - 1))
        return _finish(pool, d, D, fallback)
    if D == 4 and d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1):
        pool.append(_gq_w(d - 1))
        return _finish(pool, d, D, fallback)

    def expand(g, dl):
        """Augment with spare degree, then greedily grow both versions."""
        out = []
        aug = _augment(g[0], g[1], d, rng.randrange(1 << 30))
        out.append(aug)
        for h in (g, aug):
            sl = min(dl, time.monotonic() + slice_s)
            out.append(_grow(h[0], h[1], d, D, rng, sl))
        return out

    # Structural candidates (diameter-3 arc graphs are valid for all D >= 3).
    struct_end = at(0.12)
    arcs = _arc_candidates(d, struct_end, rng)
    pool.extend(arcs)
    if arcs:
        best_arc = max(arcs, key=lambda g: g[0])
        pool.extend(expand(best_arc, struct_end))
    if D == 3:
        er = _er_base(d)
        if er is not None:
            pool.append(er)
            pool.extend(expand(er, struct_end))
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            pool.append(gq)
            pool.extend(expand(gq, struct_end))

    # Small Haar-graph search.
    haar_end = at(0.2)
    hm, miss, hbest = d + 1, 0, None
    while time.monotonic() < haar_end and miss < 4:
        S = _search_haar(d, D, hm, rng, haar_end, 120)
        if S is not None:
            hbest = lib.haar_graph(hm, S)
            miss = 0
        else:
            miss += 1
        hm += 1
    if hbest is not None:
        pool.append(hbest)

    # Group-lift search, seeded at the best valid size found so far.
    bv = _best_valid(pool, d, D)
    start_n = bv[0] if bv is not None else 0
    gbest = _group_search(d, D, rng, at(0.6), cap, start_n)
    if gbest is not None:
        pool.append(gbest)

    # Cyclic voltage-lift annealing, one slice per base size.
    lifts = []
    cyc_end = at(0.8)
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= cyc_end:
            break
        sl_end = now + (cyc_end - now) / (len(S_LIST) - idx)
        res = _search(s, d, D, rng, sl_end, cap)
        if res is not None:
            m, P, V = res
            g = _graph(s, m, P, V, d)
            pool.append(g)
            lifts.append(g)

    # Post-process the largest cyclic lifts.
    lifts.sort(key=lambda g: -g[0])
    post_end = at(0.92)
    for g in lifts[:POST_LIFTS]:
        if time.monotonic() >= post_end:
            break
        pool.extend(expand(g, post_end))

    # Iterated remove-and-regrow on the best valid graph so far.
    if time.monotonic() < end:
        bv = _best_valid(pool, d, D)
        if bv is not None:
            pool.append(_ils(bv[0], bv[1], d, D, rng, end))

    return _finish(pool, d, D, fallback)
