import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# Bold route: Haar graphs of finite groups Z_m x| Z_k2.
#
# Vertices A_g and B_h (g, h in G). Edges A_g -- B_{g*s} for s in S, |S| = d.
# Left multiplication is an automorphism, so the diameter is checked by a
# BFS from A_e and from B_e only. The connection set S is found by local search
# that minimises the number of unreached pairs.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _group_arrays(m, k2, r):
    """Return (G, a, b, pw): element x = a*k2 + b, and pw[t] = r^t mod m."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    pw = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    return G, a, b, pw


def _mulcol(a, b, sa, sb, m, k2, pw):
    """Vector of g * s for all g = (a, b) (arrays), with s = (sa, sb) scalar.
    Product: (a, b)(c, e) = (a + r^b c, b + e)."""
    return ((a + pw[b] * sa) % m) * k2 + (b + sb) % k2


def _unreached(G, Mr, Mi, D, src):
    """Number of vertices (on both sides) not within distance D of source (src=0: A_e, src=1: B_e)."""
    seenA = np.zeros(G, dtype=bool)
    seenB = np.zeros(G, dtype=bool)
    fa = np.zeros(G, dtype=bool)
    fb = np.zeros(G, dtype=bool)
    if src == 0:
        seenA[0] = True
        fa[0] = True
    else:
        seenB[0] = True
        fb[0] = True
    for _ in range(D):
        nb = np.zeros(G, dtype=bool)
        if fa.any():
            nb[Mr[fa].ravel()] = True
            nb &= ~seenB
        na = np.zeros(G, dtype=bool)
        if fb.any():
            na[Mi[fb].ravel()] = True
            na &= ~seenA
        seenB |= nb
        seenA |= na
        fa, fb = na, nb
        if not (fa.any() or fb.any()):
            break
    return int(G - seenA.sum()) + int(G - seenB.sum())


def _cost(G, Mr, Mi, D):
    return _unreached(G, Mr, Mi, D, 0) + _unreached(G, Mr, Mi, D, 1)


def _haar_search(d, D, G, a, b, m, k2, pw, rng, deadline, iters):
    """Local search over the connection set S. Returns Mr (G x d) when diameter <= D, else None."""
    if G < d:
        return None
    S = rng.sample(range(G), d)
    Mr = np.empty((G, d), dtype=np.int64)
    Mi = np.empty((G, d), dtype=np.int64)

    def setcol(j):
        sa, sb = divmod(S[j], k2)
        Mr[:, j] = _mulcol(a, b, sa, sb, m, k2, pw)
        ib = (-sb) % k2
        ia = (-int(pw[ib]) * sa) % m          # inverse of (sa, sb) is (ia, ib)
        Mi[:, j] = _mulcol(a, b, ia, ib, m, k2, pw)

    for j in range(d):
        setcol(j)
    cost = _cost(G, Mr, Mi, D)
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        j = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[j]
        S[j] = new
        setcol(j)
        c2 = _cost(G, Mr, Mi, D)
        temp = 0.2 + 3.0 * (1.0 - it / iters)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[j] = old
            setcol(j)
    return Mr if cost == 0 else None


def _haar_edges(G, Mr):
    d = Mr.shape[1]
    return 2 * G, [(g, G + int(Mr[g, j])) for j in range(d) for g in range(G)]


# ----------------------------------------------------------------------------
# Growth by edge-switch vertex insertion (keeps every accepted graph valid).
# ----------------------------------------------------------------------------

def _colours(n, edges):
    """Proper 2-colouring of a bipartite graph (BFS); returns a list of 0/1 per vertex."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if col[w] == -1:
                    col[w] = 1 - col[u]
                    stack.append(w)
    return col


def _grow_step(n, edges, col, d, D, rng, deadline):
    """Try random edge-switch insertions until one keeps diameter <= D. Returns (n+2, edges, col) or None."""
    m = len(edges)
    need = d - 1
    while time.monotonic() < deadline:
        order = list(range(m))
        rng.shuffle(order)
        used_a, used_b, chosen = set(), set(), []
        for idx in order:
            u, v = edges[idx]
            if col[u] == 1:
                u, v = v, u
            if u in used_a or v in used_b:
                continue
            used_a.add(u)
            used_b.add(v)
            chosen.append((idx, u, v))
            if len(chosen) == need:
                break
        if len(chosen) < need:
            continue
        drop = {idx for idx, _, _ in chosen}
        new_edges = [edges[i] for i in range(m) if i not in drop]
        x, y = n, n + 1
        for _, a, b in chosen:
            new_edges.append((x, b))
            new_edges.append((a, y))
        new_edges.append((x, y))
        if lib.within_diameter(n + 2, new_edges, D):
            return n + 2, new_edges, col + [0, 1]
    return None


def _grow(d, D, n, edges, rng, deadline):
    """Repeatedly insert vertex pairs while the graph stays valid. Returns (n, edges)."""
    col = _colours(n, edges)
    while time.monotonic() < deadline:
        res = _grow_step(n, edges, col, d, D, rng, deadline)
        if res is None:
            break
        n, edges, col = res
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, degree d, and is bipartite.
    best = (2 * d, [(i, d + j) for i in range(d) for j in range(d)])
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

    if D == 4 and time.monotonic() < start + 0.3 * budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bold route: Haar graphs of semidirect products, searched by local search.
    search_deadline = start + 0.6 * budget
    slice_len = max(1.0, 0.06 * budget)
    while time.monotonic() < search_deadline:
        tgt = best_n // 2 + 1 + rng.randrange(0, max(2, best_n // 100))
        g = _sample_group(tgt, rng)
        if g is None:
            continue
        m, k2, r = g
        G, a, b, pw = _group_arrays(m, k2, r)
        if G < d or 2 * G <= best_n:
            continue
        slice_end = min(search_deadline, time.monotonic() + slice_len)
        Mr = _haar_search(d, D, G, a, b, m, k2, pw, rng, slice_end, 30000)
        if Mr is not None:
            n_, e_ = _haar_edges(G, Mr)
            consider(n_, e_)

    # Growth phase: spend the remaining time inserting vertex pairs into the best graph.
    if d >= 2 and time.monotonic() < deadline:
        gn, ge = _grow(d, D, best_n, list(best[1]), rng, deadline)
        consider(gn, ge)

    if not lib.is_valid(best[0], best[1], d, D):
        return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]
    return best
