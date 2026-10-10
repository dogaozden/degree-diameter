import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Instant algebraic families (incidence graphs of PG(2,q) and W(q)).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree is q + 1, diameter is 4, order is 2(q+1)(q^2+1).
    """
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
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Cover-based vertex extension (keeps the parent's D = 3 / D = 4 growth).
# ----------------------------------------------------------------------------

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
            for attempt in range(60):
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
# NEW FAMILY: simulated annealing over bipartite near-regular graphs.
#
# Fix the order n = 2h with parts {0..h-1} and {h..2h-1}. Start from a random
# bipartite graph with max degree d and minimise the number of vertex pairs
# at distance > D by double-edge switches (degrees and bipartiteness are kept).
#
# Distance balls are computed with packed uint64 bitsets in numpy: each vertex
# keeps a bitset of vertices reachable within r steps, and one round ORs the
# bitsets of its neighbours. Unused neighbour slots point to the vertex itself,
# which is harmless under OR.
# ----------------------------------------------------------------------------

_POP = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


def _cost(n, d, D, EL, ER):
    """Number of unordered pairs at distance > D (0 means diameter <= D and connected)."""
    M = len(EL)
    owners = np.concatenate([EL, ER])
    others = np.concatenate([ER, EL])
    order = np.argsort(owners, kind="stable")
    os_ = owners[order]
    ot = others[order]
    starts = np.searchsorted(os_, os_, side="left")
    slot = np.arange(2 * M) - starts
    nbr = np.repeat(np.arange(n, dtype=np.int64)[:, None], d, axis=1)
    nbr[os_, slot] = ot

    W = (n + 63) // 64
    R = np.zeros((n, W), dtype=np.uint64)
    ids = np.arange(n, dtype=np.int64)
    R[ids, ids >> 6] = np.left_shift(np.uint64(1), (ids & 63).astype(np.uint64))
    for _ in range(D):
        Rn = R.copy()
        for c in range(d):
            Rn |= R[nbr[:, c]]
        if np.array_equal(Rn, R):
            break
        R = Rn
    total = int(_POP[R.view(np.uint8)].sum())
    return (n * n - total) // 2


def _anneal(n, d, D, rng, deadline):
    """Anneal a bipartite graph on n vertices (n even) to diameter <= D. Returns edges or None."""
    h = n // 2
    es = set()
    EL, ER = [], []
    deg = [0] * n
    for _ in range(d):
        p = rng.sample(range(h), h)
        for i in range(h):
            a, b = i, h + p[i]
            if deg[a] < d and deg[b] < d and (a * n + b) not in es:
                es.add(a * n + b)
                EL.append(a)
                ER.append(b)
                deg[a] += 1
                deg[b] += 1
    M = len(EL)
    if M < 2:
        return None
    EL = np.array(EL, dtype=np.int64)
    ER = np.array(ER, dtype=np.int64)

    cur = _cost(n, d, D, EL, ER)
    best = cur
    best_edges = (EL.copy(), ER.copy())
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = 3.0 * (0.03 / 3.0) ** frac  # cooling schedule (unordered-pair units)

        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = int(EL[i]), int(ER[i])
        c, e = int(EL[j]), int(ER[j])
        if a == c or b == e:
            continue
        k1 = a * n + e
        k2 = c * n + b
        if k1 in es or k2 in es:
            continue

        # Double-edge switch: (a,b),(c,e) -> (a,e),(c,b).
        ER[i] = e
        ER[j] = b
        new = _cost(n, d, D, EL, ER)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            es.discard(a * n + b)
            es.discard(c * n + e)
            es.add(k1)
            es.add(k2)
            cur = new
            if cur < best:
                best = cur
                best_edges = (EL.copy(), ER.copy())
        else:
            ER[i] = b
            ER[j] = e

    if best != 0:
        return None
    BL, BR = best_edges
    return [(int(x), int(y)) for x, y in zip(BL, BR)]


def _even(x):
    return x if x % 2 == 0 else x + 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Algebraic families (instant), grown by cover extension for D = 3, 4.
    if D >= 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]
        grow_deadline = start + 0.25 * time_limit
        for i, q in enumerate(pg_qs):
            pg_n, pg_e = lib.projective_plane_incidence(q)
            consider(pg_n, pg_e)
            if D <= 4:
                slice_end = start + 0.25 * time_limit * (i + 1) / len(pg_qs)
                n2, e2 = _grow(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4:
                n2, e2 = _grow(gq[0], gq[1], d, D, grow_deadline, rng)
                consider(n2, e2)

    # Main new search: annealing over bipartite near-regular graphs, with a
    # growing target order. Successes raise the target; failures bisect back.
    if d >= 2:
        cand = _even(max(best_n + 2, int(best_n * 1.1)))
        fails = 0
        while True:
            now = time.monotonic()
            if now >= deadline - 0.2:
                break
            remaining = deadline - now
            slice_end = now + min(remaining, max(2.0, remaining / 3))
            edges = _anneal(cand, d, D, rng, slice_end)
            if edges is not None and lib.is_valid(cand, edges, d, D):
                best = (cand, edges)
                best_n = cand
                fails = 0
                cand = _even(int(cand * 1.10) + 2)
            else:
                if cand <= best_n + 2:
                    fails += 1
                    if fails >= 2:
                        break
                cand = _even((best_n + cand) // 2)
                if cand <= best_n:
                    cand = best_n + 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
