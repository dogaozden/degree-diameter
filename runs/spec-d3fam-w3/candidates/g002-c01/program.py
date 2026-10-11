import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Generic helpers.
# ----------------------------------------------------------------------------

def _color(n, adj):
    """Two-colour a bipartite graph given as adjacency collections."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _bad_count(n, adj, D):
    """Ordered count of vertex pairs at distance > D (bitmask BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


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
    return _color(n, adj)


# ----------------------------------------------------------------------------
# Vertex-pair augmentation of a diameter-3 bipartite graph (from degree-d base).
# Adds one point P and one line L, then 2-switch anneals to restore diameter.
# ----------------------------------------------------------------------------

def _augment(n, edges, d, D, rng, deadline):
    """Add two vertices (a point P and a line L) via degree-preserving 2-switch annealing.

    Returns (n+2, edges) with diameter <= D, or None if the search fails before the deadline.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1
    adj.append(set())
    adj.append(set())
    N = n + 2

    oriented = [((u, v) if col[u] == 0 else (v, u)) for u, v in edges]
    rng.shuffle(oriented)
    used, pick = set(), []
    for idx, (a, b) in enumerate(oriented):
        if a not in used and b not in used:
            pick.append(idx)
            used.add(a)
            used.add(b)
            if len(pick) == d:
                break
    if len(pick) < d:
        return None

    picked = set(pick)
    E = [oriented[i] for i in range(len(oriented)) if i not in picked]
    for idx in pick:
        a, b = oriented[idx]
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a].add(P)
        adj[P].add(a)
        adj[b].add(L)
        adj[L].add(b)
        E.append((a, P))
        E.append((L, b))

    M = len(E)
    cur = _bad_count(N, adj, D)
    T = 1.0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new = _bad_count(N, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return N, list(E)


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
    """Conic (plus nucleus for even q) as a point-index set."""
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
        if s < 1:
            continue
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)]
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
            for attempt in range(100):
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
    """Extend by cover vertices, then saturate edges with leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(6):
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
# Cyclic Haar graph search (diameter 3).
#
# Haar graph H(m, S): a_i ~ b_{i+s} for s in S, |S| = d, 0 in S.
# Diameter <= 3 iff every x in Z_m lies in S-S, and every y lies in S or S-S+S.
# ----------------------------------------------------------------------------

def _cost(a, m):
    """Number of residues missed by the a-side and b-side coverage conditions."""
    diff = (a[:, None] - a[None, :]) % m
    cov_a = np.zeros(m, dtype=bool)
    cov_a[diff.ravel()] = True
    tri = (diff[:, :, None] + a[None, None, :]) % m
    cov_b = np.zeros(m, dtype=bool)
    cov_b[tri.ravel()] = True
    cov_b[a] = True
    return int((~cov_a).sum() + (~cov_b).sum())


def _cyclic_search(d, m, rng, deadline):
    """Find S (size d, 0 in S) in Z_m satisfying the diameter-3 covering conditions, or None."""
    if d > m:
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    a = np.array(S, dtype=np.int64)
    cost = _cost(a, m)
    T = 0.6
    steps = 0
    while cost > 0:
        if steps % 256 == 0 and time.monotonic() >= deadline:
            return None
        steps += 1
        idx = rng.randrange(1, d)
        new = rng.randrange(1, m)
        if new in S:
            continue
        a2 = a.copy()
        a2[idx] = new
        c2 = _cost(a2, m)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
            S[idx] = new
            a, cost = a2, c2
    return [int(x) for x in a]


def _cyclic_phase(d, best, rng, deadline):
    """Sweep cyclic orders m upward from just above the current best, with even time shares."""
    best_n, best_edges = best
    m0 = max(d, best_n // 2 + 1)
    mcap = d * d - d + 1  # covering S-S needs d^2-d+1 >= m
    ms = list(range(m0, mcap + 1))
    for i, m in enumerate(ms):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(ms) - i)
        S = _cyclic_search(d, m, rng, now + share)
        if S is not None:
            n, edges = lib.haar_graph(m, S)
            if n > best_n and lib.is_valid(n, edges, d, 3):
                best_n, best_edges = n, edges
    return best_n, best_edges


# ----------------------------------------------------------------------------
# Degree-preserving 2-switch annealing on M+M bipartite graphs (diameter 3).
# ----------------------------------------------------------------------------

def _swap_search(d, M, rng, deadline):
    """Anneal a d-regular bipartite graph on M+M vertices to diameter 3; return edge list or None."""
    N = 2 * M
    adj = [[] for _ in range(N)]
    E = []
    for i in range(M):
        for s in range(d):
            b = M + (i + s) % M
            E.append((i, b))
            adj[i].append(b)
            adj[b].append(i)
    has = set(E)

    def set_edge(k, new):
        a, b = E[k]
        adj[a].remove(b)
        adj[b].remove(a)
        has.discard((a, b))
        a2, b2 = new
        adj[a2].append(b2)
        adj[b2].append(a2)
        has.add(new)
        E[k] = new

    def cost():
        reach = [1 << v for v in range(N)]
        for _ in range(3):
            nxt = []
            for v in range(N):
                r = reach[v]
                for u in adj[v]:
                    r |= reach[u]
                nxt.append(r)
            reach = nxt
        return sum(N - r.bit_count() for r in reach) // 2

    def try_switch(i, j):
        if i == j:
            return None
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            return None
        if (a1, b2) in has or (a2, b1) in has:
            return None
        return a1, b1, a2, b2

    for _ in range(5 * len(E)):
        if time.monotonic() >= deadline:
            return None
        res = try_switch(rng.randrange(len(E)), rng.randrange(len(E)))
        if res is None:
            continue
        a1, b1, a2, b2 = res
        i = E.index((a1, b1))
        j = E.index((a2, b2))
        set_edge(i, (a1, b2))
        set_edge(j, (a2, b1))

    cur = cost()
    T0 = 1.5
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - start) / span
        T = T0 * (0.01 ** frac)
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        res = try_switch(i, j)
        if res is None:
            continue
        a1, b1, a2, b2 = res
        set_edge(i, (a1, b2))
        set_edge(j, (a2, b1))
        new = cost()
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            set_edge(i, (a1, b1))
            set_edge(j, (a2, b2))
    if cur == 0:
        return list(E)
    return None


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used only for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
    import itertools
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
    """W(q) for the largest prime power q <= min(d - 1, 7), for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _valid_or(best, d, D, fallback):
    if lib.is_valid(best[0], best[1], d, D):
        return best
    return fallback


def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard = start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    kdd = lib.haar_graph(d, range(d))
    if not lib.is_valid(kdd[0], kdd[1], d, D):
        kdd = (1, [])
    best = kdd
    mb = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
        m, misses = d + 1, 0
        while time.monotonic() < hard and misses < 10:
            found = None
            for _ in range(30):
                if time.monotonic() >= hard:
                    break
                S = [0] + rng.sample(range(1, m), d - 1)
                n, edges = lib.haar_graph(m, S)
                if lib.within_diameter(n, edges, D):
                    found = (n, edges)
                    break
            if found:
                consider(found[0], found[1])
                misses = 0
            else:
                misses += 1
            m += 1
        return _valid_or(best, d, D, kdd)

    # D == 3 from here on.
    if best[0] >= mb:
        return _valid_or(best, d, D, kdd)

    # Structured base: PG(2, d-1) if d-1 is a prime power, else Araujo-Pardo-Lopez.
    base = None
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        base = lib.projective_plane_incidence(q)
    elif d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            base = lib.araujo_lopez_graph(d - 2)
        except Exception:
            base = None

    if base is not None:
        consider(base[0], base[1])
        cur = best
        aug_deadline = start + 0.25 * time_limit
        while time.monotonic() < aug_deadline and cur[0] + 2 <= mb:
            res = _augment(cur[0], cur[1], d, D, rng, aug_deadline)
            if res is None or not lib.is_valid(res[0], res[1], d, D):
                break
            cur = res
            consider(res[0], res[1])

    # Arc-extended projective plane graphs, then cover-growth on the best so far.
    for n_c, e_c in _arc_extensions(d, start + 0.35 * time_limit,
                                    random.Random(seed * 7919 + d)):
        consider(n_c, e_c)
    if time.monotonic() < hard:
        n2, e2 = _grow(best[0], best[1], d, D, start + 0.4 * time_limit, rng)
        consider(n2, e2)

    # Cyclic Haar search past the current best.
    if d >= 2 and best[0] < mb:
        best = _valid_or(best, d, D, kdd)
        n3, e3 = _cyclic_phase(d, best, rng, start + 0.6 * time_limit)
        consider(n3, e3)

    # Remaining time: 2-switch annealing one vertex per side larger each time.
    M = best[0] // 2 + 1
    while time.monotonic() < hard and best[0] < mb:
        E = _swap_search(d, M, rng, hard)
        if E is None:
            break
        consider(2 * M, E)
        M += 1

    return _valid_or(best, d, D, kdd)
