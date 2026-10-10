import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
GQ_Q_MAX = 9                  # largest q for which W(q) is built
G_ITERS = 500                 # hill-climb moves per group-lift attempt
COVER_TRIES = 12              # randomized cover restarts per extension step
ILS_STEP = 0.5                # seconds allowed for one remove-and-regrow step
ILS_SLACK = 2                 # ILS may wander at most this far below the best size
ILS_DOWN_P = 0.2              # chance to accept a one-vertex shrink
_BIG = 10 ** 9


# ---------------------------------------------------------------- basic graph helpers

def _adj_of(n, edges):
    """Adjacency lists (unsorted) for an edge list on vertices 0..n-1."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bipartition(n, adj):
    """Proper 2-colouring of a bipartite graph given by adjacency lists."""
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


def _largest_pp(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


# ---------------------------------------------------------------- vertex extension (cover based)

def _greedy_cover(cands, ball, full, budget, rng, randomize):
    """Greedy cover of `full` by at most `budget` candidates. Returns list or None."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < budget and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.3:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add single vertices whose neighbourhoods cover all vertices within distance D-1."""
    edges = list(edges)
    adj = _adj_of(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        sides = (0, 1) if rng.random() < 0.5 else (1, 0)
        for c in sides:
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            chosen = None
            for attempt in range(COVER_TRIES):
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


def _pair_extend(n, edges, d, D, deadline, rng):
    """Add two adjacent new vertices x, y at once (needs D >= 3)."""
    edges = list(edges)
    if D < 3 or n == 0 or d < 2:
        return n, edges
    adj = _adj_of(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        full = (1 << n) - 1
        b1 = _balls_radius(n, adj, D - 1)
        b2 = _balls_radius(n, adj, D - 2)
        placed = False
        sides = (0, 1) if rng.random() < 0.5 else (1, 0)
        for c in sides:
            side_other = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            side_c = [u for u in range(n) if color[u] == c and deg[u] < d]
            N = _greedy_cover(side_other, b1, full, d - 1, rng, False)
            if not N:
                continue
            b2N = 0
            for u in N:
                b2N |= b2[u]
            M = _greedy_cover(side_c, b1, full & ~b2N, d - 1, rng, False)
            if M is None:
                continue
            x, y = n, n + 1
            n += 2
            color.append(c)
            color.append(1 - c)
            adj.append([])
            adj.append([])
            deg.append(0)
            deg.append(0)
            for u in N:
                edges.append((u, x))
                adj[u].append(x)
                adj[x].append(u)
                deg[u] += 1
                deg[x] += 1
            for u in M:
                edges.append((u, y))
                adj[u].append(y)
                adj[y].append(u)
                deg[u] += 1
                deg[y] += 1
            edges.append((x, y))
            adj[x].append(y)
            adj[y].append(x)
            deg[x] += 1
            deg[y] += 1
            placed = True
            break
        if not placed:
            break
    return n, edges


def _saturate(n, edges, d, rng):
    """Randomly add edges between deficient opposite-colour vertices. Returns the edge list."""
    edges = list(edges)
    if n == 0:
        return edges
    adj = _adj_of(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    if not left or not right:
        return edges
    for _ in range(4 * (len(left) + len(right))):
        a = rng.choice(left)
        b = rng.choice(right)
        if deg[a] >= d or deg[b] >= d:
            continue
        key = (min(a, b), max(a, b))
        if key in existing:
            continue
        existing.add(key)
        edges.append((a, b))
        deg[a] += 1
        deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Alternate cover extension, pair extension and saturation. Every stage keeps validity."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        before = cur_n
        cur_n, cur_e = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        cur_n, cur_e = _pair_extend(cur_n, cur_e, d, D, deadline, rng)
        cur_e = _saturate(cur_n, cur_e, d, rng)
        if cur_n == before:
            break
    return cur_n, cur_e


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


# ---------------------------------------------------------------- D >= 4 : generalized quadrangle

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


# ---------------------------------------------------------------- group lifts (representative BFS)
# Group G = Z_m x|_r Z_k, element (a, b) coded as a*k + b. Left multiplication is an
# automorphism of the lift, so one BFS per base vertex decides the diameter.

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
    """Permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _gcost(k, G, D, darts, perms):
    """Number of (base representative, vertex) pairs not reached within D. Zero means valid."""
    dup = len(darts) - len({(i, j, s) for i, j, s in darts})
    if dup:
        return _BIG * (1 + dup)
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
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _gedges(k, G, darts, perms):
    """Materialise the group lift as (n, sorted edge list)."""
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _gsearch(k, G, d, D, rng, iters, deadline):
    """Hill-climb dart voltages in a random semidirect group of order about G."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, p[i], rng.randrange(order)] for p in layers for i in range(k)]
    perms = [_right_perm(mul, order, s) for _, _, s in darts]
    cost = _gcost(k, order, D, darts, perms)
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        idx = rng.randrange(len(darts))
        old_s, old_p = darts[idx][2], perms[idx]
        new_s = rng.randrange(order)
        darts[idx][2] = new_s
        perms[idx] = _right_perm(mul, order, new_s)
        c2 = _gcost(k, order, D, darts, perms)
        if c2 <= cost or rng.random() < 0.02:
            cost = c2
        else:
            darts[idx][2] = old_s
            perms[idx] = old_p
    if cost == 0:
        return _gedges(k, order, darts, perms)
    return None


# ---------------------------------------------------------------- Haar graphs (hill-climb)

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m for diameter <= D."""
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


# ---------------------------------------------------------------- iterated remove-and-regrow

def _remove_vertex(n, edges, v):
    """Return (n-1, edges) with vertex v deleted and labels compacted."""
    out = []
    for a, b in edges:
        if a == v or b == v:
            continue
        out.append((a - 1 if a > v else a, b - 1 if b > v else b))
    return n - 1, out


def _ils(n, edges, d, D, rng, end):
    """Delete a random vertex, regrow, and keep the result if it is valid and not too small."""
    cur = (n, list(edges))
    best = cur
    while time.monotonic() < end:
        n0, e0 = cur
        if n0 < 4:
            break
        v = rng.randrange(n0)
        m, e1 = _remove_vertex(n0, e0, v)
        m, e2 = _grow(m, e1, d, D, min(end, time.monotonic() + ILS_STEP), rng)
        if m < best[0] - ILS_SLACK:
            continue
        accept = m >= n0 or (m == n0 - 1 and rng.random() < ILS_DOWN_P)
        if accept and lib.is_valid(m, e2, d, D):
            cur = (m, e2)
            if m > best[0]:
                best = cur
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    start = time.monotonic()
    end_all = start + max(1.0, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    # K_{d,d} is valid for every D >= 2 and is the fallback.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    cap = min(N_CAP, lib._moore_bound(d, D))

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best, best_n = (n, e), n

    def slice_end(frac):
        return min(end_all, time.monotonic() + frac * time_limit)

    if D == 2:
        return best

    # D = 3: projective plane PG(2,q) and the polarity double cover ER_q.
    if d >= 3:
        q = _largest_pp(d - 1)
        if q is not None:
            pg = lib.projective_plane_incidence(q)
            if D == 3 and q == d - 1:
                consider(pg[0], pg[1])
                return best          # Moore-extremal
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, slice_end(0.12), rng)
            consider(n2, e2)

        if D == 3:
            qe = _largest_pp(d - 1)
            if qe is not None:
                er = _polarity_cover(qe)
                consider(er[0], er[1])
                n2, e2 = _grow(er[0], er[1], d, D, slice_end(0.12), rng)
                consider(n2, e2)

    # D >= 4: generalized quadrangle W(q).
    if D >= 4 and d >= 3:
        qg = _largest_pp(min(d - 1, GQ_Q_MAX))
        if qg is not None:
            gq = _gq_w(qg)
            if D == 4 and qg == d - 1:
                consider(gq[0], gq[1])
                return best          # generalized quadrangle, Moore-extremal
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, slice_end(0.12), rng)
            consider(n2, e2)

    # Main search: semidirect-group lifts with an adaptive order target, plus Haar graphs.
    KS = (1, 2, 3, 4)
    gst = {k: {"G": 2, "step": 1, "miss": 0} for k in KS}
    haar_m, haar_miss = d + 1, 0
    loop_end = start + 0.68 * time_limit
    while time.monotonic() < loop_end and cap >= 4:
        if D <= 4 and haar_miss < 4 and 2 * haar_m <= cap and rng.random() < 0.15:
            S = _search_haar(d, D, haar_m, rng, loop_end, 120)
            if S is not None:
                consider(*lib.haar_graph(haar_m, S))
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
            continue

        k = rng.choice(KS)
        st = gst[k]
        floor = best_n // (2 * k) + 1
        G = max(st["G"], floor, 2)
        if 2 * k * G > cap:
            G = cap // (2 * k)
            if G < 2:
                continue
        now = time.monotonic()
        att_end = min(loop_end, now + max(0.5, (loop_end - now) / 3))
        res = _gsearch(k, G, d, D, rng, G_ITERS, att_end)
        if res is not None:
            consider(res[0], res[1])
            st["G"] = G + st["step"]
            st["step"] = min(st["step"] * 2, max(1, G // 10))
            st["miss"] = 0
        else:
            st["G"] = G
            st["miss"] += 1
            if st["miss"] >= 3:
                st["step"] = 1
                st["miss"] = 0
                st["G"] = floor

    # Spend spare degree on the current best, then run iterated local search.
    if time.monotonic() < end_all:
        consider(best_n, _saturate(best_n, best[1], d, rng))
    if D >= 3 and time.monotonic() < end_all - 0.5:
        ils = _ils(best_n, best[1], d, D, rng, end_all)
        consider(ils[0], ils[1])

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
