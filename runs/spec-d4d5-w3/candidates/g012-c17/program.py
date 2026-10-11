import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Budget. All search stops at FRAC_TOTAL of time_limit so the call returns in time.
# ----------------------------------------------------------------------------
FRAC_TOTAL = 0.80
GQ_Q_MAX = 5
BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Algebraic bases: projective plane (D >= 3) and generalized quadrangle (D >= 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
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
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Cover-based vertex extension and saturation (diameter-preserving growth).
# A new vertex whose neighbours' radius-(D-1) balls cover everything keeps the
# diameter bound, and old distances only shrink when edges are added.
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
# NEW FAMILY: vectorised voltage-lift annealing over semidirect products.
#
# Vertices: A(i,g) = i*G + g  (i < k), B(j,h) = (k+j)*G + h.
# Layer L has a permutation P[L] of range(k) and voltages S[L, i] in the group.
# Dart (L, i) joins A(i,g) to B(P[L,i], g*S[L,i]) for every g. Each vertex then
# has degree exactly d, and the graph is bipartite by construction.
#
# Left multiplication is an automorphism, so distances only need to be measured
# from the 2k representatives A(i,e), B(j,e). The cost counts (representative,
# vertex) pairs not reached within D steps, computed with numpy in one pass.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 8, 10, 12])
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


def _tables(G, mul):
    """Multiplication table M[x, y] = x*y and inverse table INV, with identity 0."""
    M = np.array([[mul(x, y) for y in range(G)] for x in range(G)], dtype=np.int64)
    ar = np.arange(G)
    if not np.array_equal(M[0], ar) or not np.array_equal(M[:, 0], ar):
        return None
    INV = np.argmax(M == 0, axis=1).astype(np.int64)
    return M, INV


def _dup(P, S, d, k):
    """True if two darts from the same A-vertex share a target and voltage (double edge)."""
    for i in range(k):
        keys = set()
        for L in range(d):
            key = (int(P[L, i]), int(S[L, i]))
            if key in keys:
                return True
            keys.add(key)
    return False


def _neighbours(k, G, d, P, S, M, INV):
    """Neighbour table (N, d): row v lists the d neighbours of vertex v."""
    N = 2 * k * G
    g = np.arange(G)
    NB = np.empty((N, d), dtype=np.int64)
    for L in range(d):
        Pinv = np.empty(k, dtype=np.int64)
        Pinv[P[L]] = np.arange(k)
        for i in range(k):
            s = S[L, i]
            j = P[L, i]
            NB[i * G:(i + 1) * G, L] = (k + j) * G + M[g, s]
        for j in range(k):
            i = Pinv[j]
            s = S[L, i]
            NB[(k + j) * G:(k + j + 1) * G, L] = i * G + M[g, INV[s]]
    return NB


def _cost(k, G, D, NB):
    """Number of (representative, vertex) pairs not within distance D. Zero means valid."""
    N = NB.shape[0]
    R = np.zeros((2 * k, N), dtype=bool)
    reps = np.arange(2 * k) * G
    R[np.arange(2 * k), reps] = True
    for _ in range(D):
        nxt = R | R[:, NB].any(axis=2)
        if np.array_equal(nxt, R):
            break
        R = nxt
    return int(2 * k * N - R.sum())


def _anneal(d, D, k, G, M, INV, rng, deadline):
    """Simulated annealing over voltages and layer permutations. Returns (n, edges) or None."""
    P = np.array([rng.sample(range(k), k) for _ in range(d)], dtype=np.int64)
    S = np.array([[rng.randrange(G) for _ in range(k)] for _ in range(d)], dtype=np.int64)

    def evaluate():
        if _dup(P, S, d, k):
            return BIG
        return _cost(k, G, D, _neighbours(k, G, d, P, S, M, INV))

    cost = evaluate()
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = 2.0 * (0.05 / 2.0) ** frac
        if k == 1 or rng.random() < 0.6:
            L = rng.randrange(d)
            i = rng.randrange(k)
            old = int(S[L, i])
            new = rng.randrange(G)
            if new == old:
                continue
            S[L, i] = new
            c2 = evaluate()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                S[L, i] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            P[L, a], P[L, b] = P[L, b], P[L, a]
            c2 = evaluate()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                P[L, a], P[L, b] = P[L, b], P[L, a]

    if cost != 0:
        return None
    NB = _neighbours(k, G, d, P, S, M, INV)
    edges = [(v, int(u)) for v in range(k * G) for u in NB[v]]
    return 2 * k * G, edges


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + FRAC_TOTAL * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # K_{d,d} has diameter 2 and is the always-valid fallback.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best = fallback
    moore = lib._moore_bound(d, D)

    def consider(c):
        nonlocal best
        if c is None:
            return False
        n, e = c
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))
            return True
        return False

    # Algebraic bases, grown cheaply by cover/saturation.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg)
            if best[0] >= moore:
                return best
            consider(_grow(pg[0], pg[1], d, D, start + 0.05 * time_limit, rng))
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)
            if best[0] >= moore:
                return best
            consider(_grow(gq[0], gq[1], d, D, start + 0.10 * time_limit, rng))

    # Main search: vectorised voltage-lift annealing over random semidirect products.
    # Each accepted lift is grown by cover vertices and saturated edges. The next
    # group order is chosen to beat the current best, so every success improves it.
    ks = [1, 1, 2, 2, 3, 4, 5, 6]
    slice_len = max(1.0, 0.15 * time_limit)
    try:
        while time.monotonic() < deadline and best[0] < moore:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, 3))
            grp = _sample_group(G, rng)
            if grp is None:
                continue
            order, mul = grp
            tab = _tables(order, mul)
            if tab is None:
                continue
            M, INV = tab
            slice_end = min(deadline, time.monotonic() + slice_len)
            res = _anneal(d, D, k, order, M, INV, rng, slice_end)
            if res is None:
                continue
            consider(res)
            grow_deadline = min(deadline, time.monotonic() + 0.05 * time_limit)
            consider(_grow(res[0], res[1], d, D, grow_deadline, rng))
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
