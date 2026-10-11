import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from the parent; used as fallbacks).
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
# NEW BOLD CONSTRUCTION: nonabelian Haar graphs (bi-Cayley with k = 1).
#
# For a finite group G and connection set S (|S| = d), the Haar graph H(G, S)
# has A_g ~ B_{g s} for s in S. It is d-regular and bipartite on 2|G| vertices.
# Left translation by h maps A_g -> A_{hg}, B_g -> B_{hg}, so every A-vertex
# looks alike and every B-vertex looks alike. Diameter <= D therefore only
# needs BFS from A_1 and B_1. The parent's families used k >= 1 layered lifts;
# this family is different: a single orbit per side over a nonabelian group,
# searched by simulated annealing on the connection set alone.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k, r) for the semidirect product Z_m x| Z_k with order m*k >= target, or None."""
    ks = [1, 2, 2, 3, 4, 4, 5, 6, 6, 7, 8, 8, 9, 10, 12, 14, 16, 18, 20, 24]
    for _ in range(200):
        k = rng.choice(ks)
        m = max(2, -(-target // k))
        if k == 1:
            r = 1
        else:
            r = None
            for _ in range(80):
                c = rng.randrange(1, m)
                if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k, r
    return None


def _group_tables(m, k, r):
    """Return (G, Ts, Invs): Ts[s, g] = g*s and Invs[s, h] = g with g*s = h.

    Elements of Z_m x| Z_k are coded a*k + b, with (a, b)(c, e) = (a + r^b c, b + e).
    """
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    powers = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _search_haar(d, D, G, Ts, Invs, rng, deadline, iters):
    """Anneal over d distinct connection elements; return (2G, edges) with diameter <= D, or None."""
    N = 2 * G
    S = rng.sample(range(G), d)
    used = set(S)
    nbr = np.empty((d, N), dtype=np.int64)

    def set_row(l, s):
        nbr[l, :G] = G + Ts[s]   # A_g -> B_{g s}
        nbr[l, G:] = Invs[s]     # B_h -> A_{h s^-1}

    for l, s in enumerate(S):
        set_row(l, s)

    def reach_of():
        # bit 0: within D of representative A_1 (index 0); bit 1: within D of B_1 (index G).
        reach = np.zeros(N, dtype=np.int64)
        reach[0] = 1
        reach[G] = 2
        for _ in range(D):
            new = reach.copy()
            for l in range(d):
                new |= reach[nbr[l]]
            if np.array_equal(new, reach):
                break
            reach = new
        return reach

    def cost_of(reach):
        return 2 * N - int(np.count_nonzero(reach & 1)) - int(np.count_nonzero(reach & 2))

    reach = reach_of()
    cost = cost_of(reach)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - t / iters))
        l = rng.randrange(d)
        old = S[l]
        new = rng.randrange(G)
        if new in used:
            continue
        S[l] = new
        set_row(l, new)
        r2 = reach_of()
        c2 = cost_of(r2)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            used.discard(old)
            used.add(new)
        else:
            S[l] = old
            set_row(l, old)

    if cost != 0:
        return None
    edges = [(g, int(nbr[l, g])) for l in range(d) for g in range(G)]
    return N, edges


# ----------------------------------------------------------------------------
# Parent's redundancy-aware pair insertion (grows the order by 2 per step).
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    """Return a proper 2-colouring (list of 0/1), or None if the graph is not bipartite."""
    adj = lib.adjacency(n, edges)
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
                elif color[v] == color[u]:
                    return None
    return color


def _edge_slack(n, edges, R):
    """Per-edge redundancy: popcount of (ball_R(u) & ball_R(v)) for each edge (u, v)."""
    balls = lib._balls(n, edges, max(1, R))
    return [(balls[u] & balls[v]).bit_count() for u, v in edges]


def _extend_redundant(n, edges, d, D, rng, deadline, max_fails=60):
    """Grow the order by 2 per accepted step, preferring high-redundancy edges to remove."""
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        slack = _edge_slack(n, edges, D - 1)
        keys = [slack[t] * (0.8 + 0.4 * rng.random()) for t in range(len(edges))]
        order = sorted(range(len(edges)), key=lambda t: -keys[t])
        chosen = []
        used_a, used_b = set(), set()
        for t in order:
            if len(chosen) == d - 1:
                break
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            if a in used_a or b in used_b:
                continue
            chosen.append(t)
            used_a.add(a)
            used_b.add(b)
        if len(chosen) < d - 1:
            break
        x, y = n, n + 1
        cs = set(chosen)
        cand = [e for t, e in enumerate(edges) if t not in cs]
        for t in chosen:
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            cand.append((x, b))
            cand.append((y, a))
        cand.append((x, y))
        if lib.is_valid(n + 2, cand, d, D):
            edges = cand
            n += 2
            color.extend([0, 1])
            fails = 0
        else:
            fails += 1
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.80 * time_limit, time_limit - 6.0))
    deadline = start + budget
    search_deadline = start + 0.82 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

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
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < search_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bold search: nonabelian Haar graphs of growing order.
    while time.monotonic() < search_deadline:
        target = best_n // 2 + 1 + rng.randrange(0, max(2, best_n // 60))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k, r = g
        try:
            G, Ts, Invs = _group_tables(m, k, r)
        except Exception:
            continue
        if 2 * G <= best_n:
            continue
        try:
            res = _search_haar(d, D, G, Ts, Invs, rng, search_deadline, 12000)
        except Exception:
            res = None
        if res is not None:
            consider(res[0], res[1])

    # Spend leftover time extending the best graph by redundancy-aware insertion.
    try:
        if time.monotonic() < deadline - 1.0:
            n2, e2 = _extend_redundant(best_n, best[1], d, D, rng, deadline)
            if n2 > best_n:
                consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
