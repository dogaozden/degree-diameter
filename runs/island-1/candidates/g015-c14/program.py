import itertools
import math
import random
import time

import numpy as np

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Algebraic bases: projective plane, Araujo-Pardo-Lopez, generalized quadrangle.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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


def _largest_pp_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _araujo_candidate(d):
    q = _largest_pp_le(d - 2)
    if q is None or q < 3:
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except Exception:
        return None


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
# Cover-based vertex extension and edge saturation (diameter-preserving growth).
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
    """Greedily join deficient opposite-side vertices in random order."""
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
# Haar graph hill-climb (D = 3 secondary family).
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


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2, annealed over both
# the voltages S and the layer permutations P, with numpy-vectorised cost.
#
# Left vertices (i, g), right vertices (j, h). Layer l pairs left i with
# right P[l][i] via S[l][i]: (i, g) ~ (P[l][i], g * S[l][i]).
# Each layer is a perfect matching between blocks, so the graph is d-regular
# and bipartite by construction.
# ----------------------------------------------------------------------------

def _sample_group(lo, hi, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 with order in [lo, hi], or None."""
    for _ in range(40):
        G = rng.randrange(lo, hi + 1)
        divs = [k2 for k2 in range(1, 17) if G % k2 == 0 and G // k2 >= 2]
        if not divs:
            continue
        k2 = rng.choice(divs)
        m = G // k2
        cands = [1]  # r = 1 gives the abelian group
        if k2 > 1 and m > 2:
            cands += [r for r in rng.sample(range(2, m), min(m - 2, 120))
                      if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _rperm_cache(mul, G):
    """Return a getter s -> (p, inv) where p[g] = g*s and inv[h] = h*s^{-1}, cached per s."""
    cache = {}

    def get(s):
        if s not in cache:
            p = np.fromiter((mul(g, s) for g in range(G)), dtype=np.int64, count=G)
            inv = np.empty(G, dtype=np.int64)
            inv[p] = np.arange(G, dtype=np.int64)
            cache[s] = (p, inv)
        return cache[s]

    return get


def _build_adj(k, G, P, S, get):
    """Return the (2kG, d) neighbour array of the bi-Cayley graph."""
    d = P.shape[0]
    N = 2 * k * G
    A = np.empty((N, d), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            j = int(P[l, i])
            s = int(S[l, i])
            p, inv = get(s)
            A[i * G:(i + 1) * G, l] = (k + j) * G + p
            A[(k + j) * G:(k + j + 1) * G, l] = i * G + inv
    return A


def _cost(k, G, D, A):
    """Number of (source, vertex) pairs not reached within D steps. Zero means diameter <= D."""
    N = A.shape[0]
    total = 0
    sources = list(range(0, k * G, G)) + list(range(k * G, 2 * k * G, G))
    for src in sources:
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            mark = np.zeros(N, dtype=bool)
            mark[A[front].ravel()] = True
            mark &= ~seen
            front = np.flatnonzero(mark)
            if front.size == 0:
                break
            seen |= mark
        total += N - int(np.count_nonzero(seen))
    return total


def _anneal(d, D, k, G, mul, rng, iters, deadline):
    """Anneal voltages and layer permutations. Returns (n, edges) with zero cost, or None."""
    get = _rperm_cache(mul, G)
    P = np.array([rng.sample(range(k), k) for _ in range(d)], dtype=np.int64)
    S = np.array([[rng.randrange(G) for _ in range(k)] for _ in range(d)], dtype=np.int64)
    ar = np.arange(k, dtype=np.int64)

    def evaluate(P, S):
        keys = (ar[None, :] * k + P) * G + S
        if np.unique(keys).size < keys.size:
            return _BIG, None  # parallel edges would appear
        A = _build_adj(k, G, P, S, get)
        return _cost(k, G, D, A), A

    cost, _ = evaluate(P, S)
    best = cost
    best_P = P.copy()
    best_S = S.copy()
    T0 = 2.0

    for t in range(iters):
        if best == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.05
        if k == 1 or rng.random() < 0.5:
            l = rng.randrange(d)
            i = rng.randrange(k)
            old = int(S[l, i])
            S[l, i] = rng.randrange(G)
            c, _ = evaluate(P, S)
            if c <= cost or rng.random() < math.exp(-(c - cost) / T):
                cost = c
            else:
                S[l, i] = old
        else:
            l = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            P[l, a], P[l, b] = P[l, b], P[l, a]
            c, _ = evaluate(P, S)
            if c <= cost or rng.random() < math.exp(-(c - cost) / T):
                cost = c
            else:
                P[l, a], P[l, b] = P[l, b], P[l, a]
        if cost < best:
            best = cost
            best_P = P.copy()
            best_S = S.copy()

    if best != 0:
        return None
    _, A = evaluate(best_P, best_S)
    if A is None:
        return None
    N = A.shape[0]
    edges = []
    for a in range(k * G):
        for b in A[a].tolist():
            edges.append((a, int(b)))
    return N, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 4.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    moore = lib._moore_bound(d, D)
    rng = random.Random(seed)

    # Algebraic bases.
    bases = []
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            bases.append(pg)
        al = _araujo_candidate(d)
        if al is not None:
            bases.append(al)
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            bases.append(gq)
    for b in bases:
        consider(b[0], b[1])

    # Arc-extended projective planes (D = 3 family).
    if D >= 3 and best_n < moore:
        arc_end = start + 0.2 * (deadline - start)
        for n_c, e_c in _arc_extensions(d, arc_end, random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    # Diameter-preserving growth of the bases; smaller share for D >= 5,
    # where the lift search is the main engine.
    grow_frac = 0.3 if D <= 4 else 0.1
    grow_end = start + grow_frac * (deadline - start)
    for idx, (n0, e0) in enumerate(bases):
        if best_n >= moore:
            break
        now = time.monotonic()
        if now >= grow_end:
            break
        slice_end = now + (grow_end - now) / (len(bases) - idx)
        n1, e1 = _grow(n0, e0, d, D, slice_end, random.Random(seed + idx))
        consider(n1, e1)

    # Main search: annealed bi-Cayley lifts, plus Haar attempts for D = 3.
    ks = [1, 1, 2, 2, 3, 4, 6] if D >= 5 else [1, 2, 2, 3, 3, 4]
    haar_m, haar_miss = d + 1, 0
    fails = 0
    while time.monotonic() < deadline and best_n < moore:
        if D == 3 and haar_miss < 4 and rng.random() < 0.1:
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
        lo = max(2, base + 1)
        if 2 * k * lo > moore:
            k = 1
            lo = max(2, best_n // 2 + 1)
            if 2 * lo > moore:
                break
        # Narrow window near the current best, or a wide window that
        # widens after consecutive failures (records often need larger groups).
        if rng.random() < 0.5:
            hi = int(lo * 1.35) + 2
        else:
            spread = min(0.6, 0.04 * (1 + fails))
            hi = lo + max(2, int(base * spread))
        g = _sample_group(lo, hi, rng)
        if g is None:
            fails += 1
            continue
        G, mul = g
        run_end = min(deadline, time.monotonic() + 4.0)
        res = _anneal(d, D, k, G, mul, rng, 4000, run_end)
        if res is not None:
            consider(res[0], res[1])
            fails = 0
        else:
            fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
