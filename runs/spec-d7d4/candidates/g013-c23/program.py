import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Small graph helpers.
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bipartition(n, adj):
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


def _balls_radius(n, adj, r):
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


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): incidence graph has diameter 4, degree q+1.
# ----------------------------------------------------------------------------

def _gq_w(q):
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


def _gq_fallback(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Diameter-preserving growth (fallback path for D >= 4).
# ----------------------------------------------------------------------------

def _greedy_cover(cands, ball, full, d, rng, randomize):
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
    edges = list(edges)
    adj = _adjacency(n, edges)
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
    edges = list(edges)
    adj = _adjacency(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
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


# ----------------------------------------------------------------------------
# NEW CONSTRUCTION: bipartite Haar-type Cayley graphs over small groups.
#
# For a group G and a d-subset S of G, let A_x ~ B_{x*s} for s in S.
# Left multiplication by g is an automorphism that is transitive on each side,
# so the diameter condition only needs BFS from A_e and from B_e.
# Search over groups of order G (cyclic or Z_m x| Z_k) and over S by
# hill climbing, and bisect on G.
# ----------------------------------------------------------------------------

def _group_table(rng, G):
    opts = [k for k in range(2, 13) if G % k == 0 and G // k >= 2]
    if opts and rng.random() < 0.8:
        k = rng.choice(opts)
        m = G // k
        cands = []
        for r in rng.sample(range(1, m), min(m - 1, 60)):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append(r)
        if cands:
            r = rng.choice(cands)
            _, mul, _ = lib.semidirect_group(m, k, r)
            return [[mul(x, y) for y in range(G)] for x in range(G)]
    return [[(x + y) % G for y in range(G)] for x in range(G)]


def _haar_bad(G, M, S, D):
    # adj[x] (x < G): B-neighbours G + x*s ; adj[G + y]: A-neighbours x with x*s = y.
    adj = [[G + row[s] for s in S] for row in M]
    adjB = [[] for _ in range(G)]
    for x in range(G):
        row = M[x]
        for s in S:
            adjB[row[s]].append(x)
    adj.extend(adjB)
    bad = 0
    for src in (0, G):
        seen = bytearray(2 * G)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        bad += 2 * G - cnt
    return bad


def _haar_attempt(G, d, D, M, rng, end, max_iters):
    S = rng.sample(range(G), d)
    cur = _haar_bad(G, M, S, D)
    it = 0
    while cur > 0 and it < max_iters and time.monotonic() < end:
        it += 1
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        T = list(S)
        T[i] = new
        sc = _haar_bad(G, M, T, D)
        if sc <= cur or rng.random() < 0.01:
            S, cur = T, sc
    return S if cur == 0 else None


def _probe(G, d, D, rng, end):
    while time.monotonic() < end:
        M = _group_table(rng, G)
        S = _haar_attempt(G, d, D, M, rng, end, 3000)
        if S is not None:
            return M, S
    return None


def _haar_search(d, D, deadline, rng, consider, lo):
    hi = lib._moore_bound(d, D) // 2 + 1
    lo = max(lo, 2)
    while hi - lo > 1 and time.monotonic() < deadline:
        mid = (lo + hi) // 2
        slice_end = min(deadline, time.monotonic() + 3.0)
        res = _probe(mid, d, D, rng, slice_end)
        if res is not None:
            M, S = res
            edges = [(x, mid + M[x][s]) for x in range(mid) for s in S]
            consider(2 * mid, edges)
            lo = mid
        else:
            hi = mid


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    start = time.monotonic()
    total = max(2.0, 0.75 * time_limit)
    deadline = start + total
    rng = random.Random(seed * 1000003 + 97 * d + D)

    n0, e0 = lib.haar_graph(d, range(d))  # K_{d,d}: safe fallback for D >= 2
    st = {"best": (n0, e0)}

    def consider(n, e):
        if n > st["best"][0] and lib.is_valid(n, e, d, D):
            st["best"] = (n, e)

    try:
        if D == 2:
            pass  # K_{d,d} is Moore-optimal for D = 2
        elif d == 2:
            m = 2 * D
            consider(m, [(i, (i + 1) % m) for i in range(m)])
        elif D == 3 and lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
        else:
            if D >= 4:
                g = _gq_fallback(d)
                if g is not None:
                    consider(g[0], g[1])
                    ext_n, ext_e = _extend_cover(g[0], g[1], d, D, start + 0.3 * total, rng)
                    consider(ext_n, _saturate_edges(ext_n, ext_e, d, rng))
            _haar_search(d, D, deadline, rng, consider, st["best"][0] // 2)
    except Exception:
        pass

    n, e = st["best"]
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
