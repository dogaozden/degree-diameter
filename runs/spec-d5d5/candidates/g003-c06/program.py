import itertools
import math
import random
import time

import numpy as np

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Structured baselines (safe fallbacks).
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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group voltage lifts (bi-Cayley over semidirect products) with simulated
# annealing over the voltages. Left multiplication by any group element is an
# automorphism, so diameter <= D iff BFS of depth D from each of the 2k base
# representatives reaches every vertex.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
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
    return [mul(g, s) for g in range(G)]


def _group_cost(k, G, D, darts, perms):
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


def _group_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _group_search(d, D, k, G, rng, iters, deadline):
    """Simulated annealing over voltages in a random group of order about G."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    G = order
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = []
    for p in layers:
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _group_cost(k, G, D, darts, perms)
    best_cost = cost
    best_state = ([list(x) for x in darts], list(perms))

    T0, T_floor = 3.0, 0.05
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_floor, T0 * (1.0 - it / iters))
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_perm = perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = _right_perm(mul, G, new_s)
        c2 = _group_cost(k, G, D, darts, perms)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_state = ([list(x) for x in darts], list(perms))
        else:
            darts[idx][2] = old_s
            perms[idx] = old_perm

    if best_cost == 0:
        darts, perms = best_state
        return _group_edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Unstructured simulated annealing over bipartite d-regular graphs with h
# vertices per side. Moves are degree-preserving edge switches. Cost is the
# number of ordered vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _ball_zeros(M, D):
    """Count ordered pairs (u, v) with dist(u, v) > D. M is adjacency with ones on the diagonal."""
    P = M
    for _ in range(D - 1):
        P = (P @ M > 0).astype(np.float32)
    return P.size - int(np.count_nonzero(P))


def _set(M, h, a, b, v):
    M[a, h + b] = v
    M[h + b, a] = v


def _sa_search(d, D, h, rng, deadline):
    """Anneal a bipartite d-regular graph on h+h vertices to diameter <= D. Returns (n, edges) or None."""
    n = 2 * h
    E = [(a, (a + s) % h) for a in range(h) for s in range(d)]
    Eset = set(E)
    M = np.zeros((n, n), dtype=np.float32)
    np.fill_diagonal(M, 1.0)
    for a, b in E:
        _set(M, h, a, b, 1.0)

    cur = _ball_zeros(M, D)
    if cur == 0:
        return n, [(a, h + b) for a, b in E]

    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    m = len(E)
    while True:
        now = time.monotonic()
        if now > deadline:
            return None
        frac = (now - t0) / span
        T = 2.0 * (1.0 - frac) + 0.1

        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in Eset or (a2, b1) in Eset:
            continue

        _set(M, h, a1, b1, 0.0)
        _set(M, h, a2, b2, 0.0)
        _set(M, h, a1, b2, 1.0)
        _set(M, h, a2, b1, 1.0)

        new = _ball_zeros(M, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            Eset.discard((a1, b1))
            Eset.discard((a2, b2))
            Eset.add((a1, b2))
            Eset.add((a2, b1))
            E[i] = (a1, b2)
            E[j] = (a2, b1)
            if cur == 0:
                return n, [(a, h + b) for a, b in E]
        else:
            _set(M, h, a1, b2, 0.0)
            _set(M, h, a2, b1, 0.0)
            _set(M, h, a1, b1, 1.0)
            _set(M, h, a2, b2, 1.0)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)
    np.random.seed(seed & 0xFFFFFFFF)

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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Stage 1: annealed group voltage lifts, targeting orders just above the best.
    if D >= 2:
        group_deadline = start + 0.45 * budget
        while time.monotonic() < group_deadline:
            k = rng.choice([1, 1, 1, 2, 2, 3])
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
            try:
                res = _group_search(d, D, k, G, rng, 2000, group_deadline)
            except Exception:
                res = None
            if res is not None:
                consider(res[0], res[1])

    # Stage 2: unstructured annealing aimed at orders just above the current best.
    if D >= 3 and time.monotonic() < deadline:
        h = max(d, best_n // 2 + 1)
        while time.monotonic() < deadline and 2 * h <= 700:
            try:
                res = _sa_search(d, D, h, rng, deadline)
            except Exception:
                res = None
            if res is None:
                break
            consider(res[0], res[1])
            h = max(h + 1, best_n // 2 + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
