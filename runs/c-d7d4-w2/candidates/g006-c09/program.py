import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases (kept from the parent as a warm start).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    """Generalized quadrangle incidence graph W(q), largest prime power q with q + 1 <= d, q <= 16."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Cover growth (kept from the parent): add vertices whose neighbourhoods cover
# the deficient vertices within distance D-1, then saturate spare degree.
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
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
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
    """Greedy set cover of `full` by at most d candidate vertices. Returns list or None."""
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


def _extend_cover(n, edges, d, D, deadline, rng, attempts):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
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
            for attempt in range(attempts):
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
    """Greedily join deficient opposite-side vertices. Keeps bipartiteness and degree <= d."""
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


def _grow(n, edges, d, D, deadline, rng, attempts=30):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, attempts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW (bold): Cayley double covers over non-abelian groups.
#
# For a group G of order N and a set S of d distinct elements, the graph with
# vertices (x, 0), (x, 1) for x in G and edges (x, 0)-(x*g, 1) for g in S is
# bipartite, d-regular and simple. Left multiplication is an automorphism that
# is transitive on each side, so the diameter is at most D exactly when every
# vertex is within distance D of (e, 0) and of (e, 1). That check is a single
# pair of BFS runs, so a hill-climb over S is cheap.
#
# Groups: cyclic Z_N and semidirect products Z_m x| Z_k (lib.semidirect_group).
# Orders are chosen just above the current best, so each success is a strict
# improvement.
# ----------------------------------------------------------------------------

def _ecc_cost(N, T, Ginv, S, D):
    """Number of (vertex, source) pairs at distance > D from the two identity vertices."""
    Sinv = [Ginv[g] for g in S]
    total = 0
    for src in (0, 1):
        s0 = bytearray(N)
        s1 = bytearray(N)
        if src == 0:
            s0[0] = 1
            f0, f1 = [0], []
        else:
            s1[0] = 1
            f0, f1 = [], [0]
        for _ in range(D):
            if not f0 and not f1:
                break
            n0, n1 = [], []
            for x in f0:
                row = T[x]
                for g in S:
                    y = row[g]
                    if not s1[y]:
                        s1[y] = 1
                        n1.append(y)
            for y in f1:
                row = T[y]
                for h in Sinv:
                    x = row[h]
                    if not s0[x]:
                        s0[x] = 1
                        n0.append(x)
            f0, f1 = n0, n1
        total += 2 * N - sum(s0) - sum(s1)
    return total


def _cayley_try(N, mul, inv, d, D, slice_end, rng):
    """Hill-climb a d-subset S of G so that the Cayley double cover has diameter <= D.

    Returns S on success, None if the time slice runs out.
    """
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    Ginv = [inv(g) for g in range(N)]
    S = rng.sample(range(N), d)
    cur = _ecc_cost(N, T, Ginv, S, D)
    stall = 0
    while cur > 0:
        if time.monotonic() >= slice_end:
            return None
        i = rng.randrange(d)
        g = rng.randrange(N)
        if g in S:
            continue
        old = S[i]
        S[i] = g
        c = _ecc_cost(N, T, Ginv, S, D)
        if c <= cur or rng.random() < 0.01:
            stall = 0 if c < cur else stall + 1
            cur = c
        else:
            S[i] = old
            stall += 1
        if stall > 400:
            S = rng.sample(range(N), d)
            cur = _ecc_cost(N, T, Ginv, S, D)
            stall = 0
    return list(S)


def _group_options(N):
    """Cyclic group plus every semidirect Z_m x| Z_k of order N (k >= 2, m >= 2)."""
    opts = [("cyc",)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append(("sd", m, k, r))
    return opts


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    moore = lib.moore_bound(d, D)

    # Stage A (short): structured warm start with cover growth.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.2 * time_limit, rng)
            consider(n1, e1)

    # Stage B (main): Cayley double covers over groups of order just above best/2.
    if D >= 2:
        while time.monotonic() < deadline:
            lo = max(best_n // 2 + 1, d)
            hi = moore // 2
            if lo > hi:
                break
            N = rng.randint(lo, min(hi, lo + 12))
            opts = _group_options(N)
            if not opts:
                continue
            opt = rng.choice(opts)
            if opt[0] == "cyc":
                _, mul, inv = lib.cyclic_group(N)
            else:
                _, mul, inv = lib.semidirect_group(opt[1], opt[2], opt[3])
            slice_end = min(deadline, time.monotonic() + 2.0)
            S = _cayley_try(N, mul, inv, d, D, slice_end, rng)
            if S is not None:
                edges = [(x, N + mul(x, g)) for x in range(N) for g in S]
                consider(2 * N, edges)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
