import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Classical bases: projective plane and generalized quadrangle incidence graphs.
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


# ----------------------------------------------------------------------------
# Diameter-preserving growth by cover vertices and spare-degree edges.
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
    """Extend by cover vertices, then saturate edges with the leftover spare degree."""
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
# NEW family: Haar graphs over NON-ABELIAN groups, searched directly.
#
# For a finite group G of order N and a d-subset S of G, let the bipartite
# graph have vertices a_g and b_x (g, x in G) with a_g ~ b_{g s} for s in S.
# Left multiplication by h maps a_g -> a_{hg}, b_x -> b_{hx}, so G acts
# transitively on each side. Hence the diameter is at most D iff the
# eccentricity bound holds from a_1 and from b_1, i.e. two BFS runs.
# Degree is |S| on both sides, the graph is bipartite, and the order is 2N.
# Groups are semidirect products Z_m x| Z_k (r = 1 gives direct products).
# ----------------------------------------------------------------------------

def _group_candidates(N, rng, limit):
    """Semidirect-product parameters (m, k, r) with m * k = N, m >= 2, r^k = 1 mod m."""
    cands = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        rng.shuffle(rs)
        for r in rs[:4]:
            cands.append((m, k, r))
    rng.shuffle(cands)
    return cands[:limit]


def _haar_bad(N, M, inv, S, D):
    """Number of (source, vertex) pairs not reached within D from a_0 and b_0. Zero means valid."""
    Sinv = [inv[s] for s in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = M[u]
                    for s in S:
                        v = N + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = M[u - N]
                    for si in Sinv:
                        v = row[si]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - cnt
    return total


def _anneal_S(N, M, inv, d, D, rng, deadline, iters):
    """Simulated annealing over d-subsets S of the group; returns a valid S or None."""
    if d > N:
        return None
    S = rng.sample(range(N), d)
    c = _haar_bad(N, M, inv, S, D)
    T = 1.5
    for it in range(iters):
        if c == 0:
            return S
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        T2 = list(S)
        T2[i] = x
        c2 = _haar_bad(N, M, inv, T2, D)
        if c2 <= c or rng.random() < math.exp((c - c2) / T):
            S, c = T2, c2
        T = max(0.15, T * 0.998)
    return S if c == 0 else None


def _haar_edges(N, M, S):
    """Edges of the bi-Cayley graph: a_g ~ b_{g s} for s in S."""
    edges = [(g, N + M[g][s]) for g in range(N) for s in S]
    return 2 * N, edges


def _group_haar_search(d, D, rng, deadline, N0, iters, consider):
    """Climb the group order N upward from N0, searching S in each group; report every hit."""
    N = max(N0, d)
    while time.monotonic() < deadline:
        hit = None
        for (m, k, r) in _group_candidates(N, rng, 6):
            if time.monotonic() >= deadline:
                break
            order, mul, _ = lib.semidirect_group(m, k, r)
            M = [[mul(x, y) for y in range(order)] for x in range(order)]
            inv = [row.index(0) for row in M]
            S = _anneal_S(N, M, inv, d, D, rng, deadline, iters)
            if S is not None:
                hit = (M, S)
                break
        if hit is not None:
            n, e = _haar_edges(N, hit[0], hit[1])
            consider(n, e)
        N += 1


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.08 * time_limit, rng)
            consider(n2, e2)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: Haar-type bi-Cayley graphs over non-abelian semidirect products.
    if D >= 4:
        _group_haar_search(d, D, rng, start + 0.85 * time_limit,
                           N0=best_n // 2 + 1, iters=800, consider=consider)

    # Diameter-preserving growth on the best graph found.
    if D >= 3:
        gn, ge = _grow(best[0], best[1], d, D, start + 0.92 * time_limit, rng)
        consider(gn, ge)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
