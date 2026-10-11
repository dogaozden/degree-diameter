import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Helpers: projective plane, generalized quadrangle and Araujo-Pardo-Lopez bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_best(d):
    """Araujo-Pardo-Lopez graph for the largest prime power q <= d - 2 (degree q + 2 <= d, diameter 3)."""
    for q in range(min(d - 2, 23), 2, -1):
        if lib.is_prime_power(q):
            try:
                return lib.araujo_lopez_graph(q)
            except ValueError:
                return None
    return None


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
# Bipartite double covers of undirected Kautz graphs.
# ----------------------------------------------------------------------------

def _kautz_undirected(s, L):
    """Adjacency lists of the undirected Kautz graph K(s, L) (L >= 2)."""
    words = []

    def rec(w):
        if len(w) == L:
            words.append(w)
            return
        for c in range(s):
            if not w or c != w[-1]:
                rec(w + (c,))

    rec(())
    idx = {w: i for i, w in enumerate(words)}
    adj = [set() for _ in words]
    for w in words:
        i = idx[w]
        for c in range(s):
            if c != w[-1]:
                j = idx[w[1:] + (c,)]
                if i != j:
                    adj[i].add(j)
                    adj[j].add(i)
    return [sorted(a) for a in adj]


def _double_cover(N, adj):
    """Bipartite double cover: vertex v -> v (side 0) and N + v (side 1); edge uv -> (u, N+v), (v, N+u)."""
    edges = []
    for u in range(N):
        for v in adj[u]:
            edges.append((u, N + v))
    return 2 * N, edges


def _kautz_cover_candidates(d, D, deadline):
    """Double covers of undirected Kautz graphs with max degree <= d, for L in {D, D-1}."""
    out = []
    cap = lib.moore_bound(d, D)
    for s in range(2, d // 2 + 2):
        if 2 * (s - 1) > d:
            break
        for L in (D, D - 1):
            if L < 2 or time.monotonic() > deadline:
                continue
            N = s * (s - 1) ** (L - 1)
            if 2 * N > cap:
                continue
            adj = _kautz_undirected(s, L)
            if not adj or max(len(a) for a in adj) > d:
                continue
            out.append(_double_cover(len(adj), adj))
    return out


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


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
    """Old PG incidence plus a new A and a new B vertex per element of S."""
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


def _arc_extensions(d, deadline, rng):
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Cover-based vertex extension (diameter-preserving growth).
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of the graph."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (returns edge list)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices first, then saturate edges with the leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Twin cloning into spare degree (diameter-preserving, bipartite-preserving).
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, D, rng):
    """Add false twins of vertices whose neighbours all have spare degree."""
    if D < 2:
        return n, list(edges)
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    order = [w for w in range(n) if adj[w]]
    rng.shuffle(order)
    for w in order:
        while adj[w] and all(deg[u] < d for u in adj[w]):
            v = n
            n += 1
            nbrs = list(adj[w])
            adj.append(nbrs)
            deg.append(len(nbrs))
            for u in nbrs:
                adj[u].append(v)
                deg[u] += 1
                edges.append((u, v))
    return n, edges


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts, evaluated with numpy.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,g*s for every g. Left multiplication by
# the group is an automorphism, so distances only need checking from the 2k
# representatives A_i,e and B_j,e. Each layer of d darts gives a permutation
# of i -> j, so the lift is d-regular on both sides.
#
# Cost = number of (representative, vertex) pairs not reached within D.
# All representatives are advanced together as a boolean matrix, with one
# vectorized gather per BFS round.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


class _Group:
    """Right-multiplication permutations and their inverses, cached per element."""

    def __init__(self, G, mul):
        self.G = G
        self.mul = mul
        self._p = {}
        self._ip = {}

    def perm(self, s):
        p = self._p.get(s)
        if p is None:
            p = np.fromiter((self.mul(g, s) for g in range(self.G)),
                            dtype=np.int64, count=self.G)
            self._p[s] = p
            self._ip[s] = np.argsort(p)
        return p

    def invperm(self, s):
        self.perm(s)
        return self._ip[s]


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


def _build_nbr(k, G, darts, grp, d):
    """Regular neighbour array of shape (2kG, d) for the bi-Cayley lift."""
    nbr = np.empty((2 * k * G, d), dtype=np.int64)
    col_a = [0] * k
    col_b = [0] * k
    for i, j, s in darts:
        p = grp.perm(s)
        ip = grp.invperm(s)
        ca = col_a[i]
        col_a[i] += 1
        cb = col_b[j]
        col_b[j] += 1
        nbr[i * G:(i + 1) * G, ca] = (k + j) * G + p
        nbr[(k + j) * G:(k + j + 1) * G, cb] = i * G + ip
    return nbr


def _cost_np(k, G, darts, grp, d, D):
    """Unreached (representative, vertex) pairs within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    nbr = _build_nbr(k, G, darts, grp, d)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    S = len(reps)
    R = np.zeros((S, N), dtype=bool)
    R[np.arange(S), reps] = True
    for _ in range(D):
        if R.all():
            break
        R = R | R[:, nbr].any(axis=2)
    return int(S * N - R.sum())


def _edges_from(k, G, darts, grp):
    E = []
    for i, j, s in darts:
        p = grp.perm(s)
        E.extend(zip(range(i * G, (i + 1) * G), ((k + j) * G + p).tolist()))
    return 2 * k * G, E


def _anneal_np(d, D, k, G, grp, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments.

    Metropolis acceptance is drawn up front, as in a threshold test: a move with
    new cost c2 is accepted iff c2 <= cost - T*ln(u). The temperature decays
    geometrically from 1.0 to 0.05 over the run.
    """
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost_np(k, G, darts, grp, d, D)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.05 ** (it / iters))
        u = 1.0 - rng.random()
        limit = cost - T * math.log(u)

        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            darts[idx][2] = new_s
            c2 = _cost_np(k, G, darts, grp, d, D)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost_np(k, G, darts, grp, d, D)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges_from(k, G, darts, grp)
    return None


# ----------------------------------------------------------------------------
# Haar graph hill-climb (small D, secondary family).
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is Moore-optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    # Exact Moore-optimal case: PG(2, d-1) incidence graph for D = 3.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    def consider_grown(n, e):
        consider(n, e)
        if time.monotonic() < deadline:
            n2, e2 = _twin_grow(n, e, d, D, rng)
            if n2 > n:
                e2 = _saturate_edges(n2, e2, d, rng)
                consider(n2, e2)

    try:
        # Kautz double covers (any D >= 2).
        kautz_deadline = start + 0.15 * time_limit
        for n_c, e_c in _kautz_cover_candidates(d, D, start + 0.08 * time_limit):
            consider(n_c, e_c)
            e_s = _saturate_edges(n_c, e_c, d, rng)
            consider(n_c, e_s)
            n2, e2 = _grow(n_c, e_s, d, D, kautz_deadline, rng)
            consider_grown(n2, e2)

        if D >= 3:
            ara = _araujo_best(d)
            if ara is not None:
                consider_grown(ara[0], ara[1])
                n2, e2 = _grow(ara[0], ara[1], d, D, start + 0.2 * time_limit, rng)
                consider_grown(n2, e2)
            pg = _best_pg(d)
            if pg is not None:
                consider_grown(pg[0], pg[1])
                n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.25 * time_limit, rng)
                consider_grown(n2, e2)
            for n_c, e_c in _arc_extensions(d, start + 0.3 * time_limit,
                                            random.Random(seed * 7919 + d)):
                consider_grown(n_c, e_c)

        if D >= 4:
            gq = _best_gq(d)
            if gq is not None:
                consider_grown(gq[0], gq[1])
                n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.35 * time_limit, rng)
                consider_grown(n2, e2)

        # Main search: annealed bi-Cayley lifts over semidirect products.
        # Larger base graphs (k up to 5) are sampled for D >= 5.
        ks = [1, 2, 2, 3, 3, 4, 5] if D >= 5 else [1, 1, 2, 3]
        haar_m, haar_miss = d + 1, 0
        span = 0.125
        SPAN_MIN, SPAN_MAX = 1.0 / 16, 0.5
        while time.monotonic() < deadline:
            if D <= 4 and haar_miss < 4 and rng.random() < 0.1:
                S = _search_haar(d, D, haar_m, rng, deadline, 120)
                if S is not None:
                    n, e = lib.haar_graph(haar_m, S)
                    consider(n, e)
                    haar_miss = 0
                else:
                    haar_miss += 1
                haar_m += 1
                continue

            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, int(base * span) + 1)))
            g = _sample_group(G, rng)
            if g is None:
                span = max(SPAN_MIN, span * 0.9)
                continue
            order, mul = g
            grp = _Group(order, mul)
            res = _anneal_np(d, D, k, order, grp, rng, deadline, iters=3000)
            if res is not None and res[0] > best_n:
                consider_grown(res[0], res[1])
                span = min(SPAN_MAX, span * 1.25)
            elif res is not None:
                consider_grown(res[0], res[1])
            else:
                span = max(SPAN_MIN, span * 0.9)
    except Exception:
        # Any failure in a search stage keeps the best valid graph found so far.
        pass

    # Final polish: twin cloning into spare degree, then saturation.
    try:
        if D >= 2:
            n2, e2 = _twin_grow(best[0], best[1], d, D, rng)
            if n2 > best[0]:
                e2 = _saturate_edges(n2, e2, d, rng)
                consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
