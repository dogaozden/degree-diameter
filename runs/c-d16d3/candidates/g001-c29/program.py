import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Strategy overview
#
# 1. Arc-extended projective plane graphs (diameter 3). Known-good baseline.
# 2. Generalized quadrangle W(q) for D >= 4. Known-good baseline.
# 3. NEW: vertex-deletion search on PG(2, Q), Q = smallest prime power >= d.
#    PG(2, Q) is (Q+1)-regular with diameter 3. For d < Q+1 we delete a set X of
#    vertices so every kept vertex loses enough neighbours (degree <= d) and the
#    kept graph still has diameter <= D. Simulated annealing over swaps keeps
#    |X| fixed; whenever the cost reaches zero we restore one deleted vertex and
#    continue, so the kept order only grows.
# 4. Annealed bi-Cayley voltage lifts (parent's search) use the remaining time.
#
# Every candidate is checked with lib.is_valid before it can replace the fallback.
# ----------------------------------------------------------------------------


# ----------------------------------------------------------------- arc extensions

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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
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
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ------------------------------------------------------------ generalized quadrangle

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


# ------------------------------------------------------ vertex-deletion search (NEW)

def _next_prime_power_at_least(x):
    q = max(2, x)
    while not lib.is_prime_power(q):
        q += 1
    return q


def _adjacency_matrix(N, edges):
    A = np.zeros((N, N), dtype=np.float32)
    nb = [[] for _ in range(N)]
    for u, v in edges:
        A[u, v] = 1.0
        A[v, u] = 1.0
        nb[u].append(v)
        nb[v].append(u)
    return A, nb


def _evaluate(A, kept, d, D):
    """Cost of the induced subgraph on kept vertices.

    cost = 2 * (total degree excess over d) + (number of unordered kept pairs at distance > D).
    Returns (cost, per-vertex excess, per-vertex bad-pair count).
    """
    K = np.outer(kept, kept)
    Ak = A * K
    deg = Ak.sum(axis=1)
    viol = np.maximum(deg - d, 0.0) * kept
    M = Ak + np.diag(kept)          # walks of length <= 1 (including staying put)
    R = M
    for _ in range(D - 1):
        R = R @ M                    # R[i, j] > 0 iff dist(i, j) <= D (kept vertices)
    bad_mask = (R <= 0) & (K > 0)
    bad_rows = bad_mask.sum(axis=1).astype(np.float64)
    cost = 2.0 * float(viol.sum()) + float(bad_rows.sum()) / 2.0
    return cost, viol, bad_rows


def _deletion_search(N, A, nb, d, D, k_target, deadline, rng):
    """Find a kept mask with as many kept vertices as possible (valid degree and distance).

    Returns the best valid kept mask (float32 0/1 vector) or None.
    """
    kept = np.ones(N, dtype=np.float32)

    # Greedy repair of degree excess: delete kept neighbours of over-degree vertices.
    while True:
        deg = A @ kept
        viol = ((kept > 0) & (deg > d)).astype(np.float32)
        if not viol.any():
            break
        score = A @ viol
        noise = np.array([rng.random() for _ in range(N)], dtype=np.float64) * 0.5
        cand = (kept > 0) & (score > 0)
        if not cand.any():
            break
        val = np.where(cand, score + noise, -1.0)
        kept[int(np.argmax(val))] = 0

    deleted_now = int(N - kept.sum())
    k = max(k_target, deleted_now)
    while int(N - kept.sum()) < k:
        alive = np.flatnonzero(kept > 0)
        if len(alive) == 0:
            return None
        kept[int(alive[rng.randrange(len(alive))])] = 0

    cost, viol, bad = _evaluate(A, kept, d, D)
    best = None
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)

    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        if cost == 0.0:
            best = kept.copy()
            dead = np.flatnonzero(kept == 0)
            if len(dead) == 0:
                break
            y = int(dead[rng.randrange(len(dead))])
            kept[y] = 1                       # shrink the deleted set by one
            cost, viol, bad = _evaluate(A, kept, d, D)
            continue

        frac = (now - t0) / span
        T = max(0.2, 1.5 * (1.0 - frac))
        weight = viol + bad
        cand = np.flatnonzero((kept > 0) & (weight > 0))
        alive = np.flatnonzero(kept > 0)
        dead = np.flatnonzero(kept == 0)
        if len(dead) == 0 or len(alive) == 0:
            break

        if len(cand) and rng.random() < 0.8:
            w = int(cand[rng.randrange(len(cand))])
            nbk = [x for x in nb[w] if kept[x] > 0]
            if nbk and rng.random() < 0.85:
                x = nbk[rng.randrange(len(nbk))]
            else:
                x = int(alive[rng.randrange(len(alive))])
        else:
            x = int(alive[rng.randrange(len(alive))])
        y = int(dead[rng.randrange(len(dead))])

        kept[x] = 0
        kept[y] = 1
        c2, v2, b2 = _evaluate(A, kept, d, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
            cost, viol, bad = c2, v2, b2
        else:
            kept[x] = 1
            kept[y] = 0
    return best


def _deletion_graph(base_n, base_edges, d, D, target_n, deadline, rng):
    """Run the deletion search on a PG base graph; return (n, edges) or None."""
    if target_n > base_n:
        return None
    A, nb = _adjacency_matrix(base_n, base_edges)
    kept = _deletion_search(base_n, A, nb, d, D, base_n - target_n, deadline, rng)
    if kept is None:
        return None
    idx = np.cumsum(kept) - 1
    n = int(kept.sum())
    E = []
    for u, v in base_edges:
        if kept[u] > 0 and kept[v] > 0:
            E.append((int(idx[u]), int(idx[v])))
    return n, E


# --------------------------------------------- simulated annealing over voltage lifts

_BIG = 10 ** 9


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
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost_lift(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
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
    return total


def _edges_lift(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost_lift(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost_lift(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost_lift(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges_lift(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.8 * time_limit
    rng = random.Random(seed)

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

    # Baseline 1: arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        for n_c, e_c in sorted(_arc_extensions(d, start + 0.3 * time_limit,
                                               random.Random(seed * 7919 + d)),
                               key=lambda t: -t[0]):
            consider(n_c, e_c)

    # Baseline 2: generalized quadrangle (diameter 4).
    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # NEW: delete vertices from PG(2, Q) with Q >= d, aiming above the current best.
    if D >= 3 and d >= 2 and D <= 6:
        Q = _next_prime_power_at_least(d)
        base_N = 2 * (Q * Q + Q + 1)
        if base_N <= 800 and best_n + 1 <= base_N:
            now = time.monotonic()
            dl = now + 0.6 * max(0.0, end - now)
            base_n, base_edges = lib.projective_plane_incidence(Q)
            res = _deletion_graph(base_n, base_edges, d, D, best_n + 1, dl,
                                  random.Random(seed * 104729 + d))
            if res is not None:
                consider(res[0], res[1])

    # Voltage lifts over semidirect products with the remaining time.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < end:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, end, iters=400)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
