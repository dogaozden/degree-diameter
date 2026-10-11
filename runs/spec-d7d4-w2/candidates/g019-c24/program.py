import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Helpers.
# ----------------------------------------------------------------------------

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


def _saturate(n, edges, d, rng):
    """Add random cross-side edges between vertices with spare degree.
    Adding edges never increases diameter and keeps the graph bipartite."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
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


# ----------------------------------------------------------------------------
# New construction: random cyclic voltage lifts of small bipartite d-regular
# base multigraphs, searched by hill climbing on the diameter defect.
#
# Base: b "A" vertices and b "B" vertices. Layer k is a permutation pi_k of
# range(b), so every base vertex has exactly d darts. Dart (A_i, B_{pi_k(i)})
# carries voltage volt[k][i] in Z_m. The lift has 2*b*m vertices, is bipartite
# by construction, and has max degree d.
#
# The lift is invariant under translation by Z_m, so the diameter is <= D iff
# every base vertex reaches all vertices within D steps from its representative
# (vertex u*m). The defect is the total count of unreached (rep, vertex) pairs.
# ----------------------------------------------------------------------------

def _lift_score(b, m, d, D, perms, volt):
    n = 2 * b * m
    N = np.empty((n, d), dtype=np.int64)
    g = np.arange(m, dtype=np.int64)
    for k in range(d):
        pk, vk = perms[k], volt[k]
        for i in range(b):
            A = i * m + g
            Bv = (b + pk[i]) * m + (g + vk[i]) % m
            N[A, k] = Bv
            N[Bv, k] = A
    nb = 2 * b
    R = np.zeros((nb, n), dtype=bool)
    idx = np.arange(nb)
    R[idx, idx * m] = True
    for _ in range(D):
        R = R | R[:, N].any(axis=2)
    return nb * n - int(R.sum())


def _try_lift(b, m, d, D, deadline, rng):
    perms = []
    for _ in range(d):
        p = list(range(b))
        rng.shuffle(p)
        perms.append(p)
    volt = [[rng.randrange(m) for _ in range(b)] for _ in range(d)]
    cur = _lift_score(b, m, d, D, perms, volt)
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        k = rng.randrange(d)
        i = rng.randrange(b)
        if b > 1 and rng.random() < 0.4:
            i2 = rng.randrange(b)
            pk = perms[k]
            pk[i], pk[i2] = pk[i2], pk[i]
            s = _lift_score(b, m, d, D, perms, volt)
            if s <= cur or rng.random() < 0.01:
                cur = s
            else:
                pk[i], pk[i2] = pk[i2], pk[i]
        else:
            old = volt[k][i]
            volt[k][i] = rng.randrange(m)
            s = _lift_score(b, m, d, D, perms, volt)
            if s <= cur or rng.random() < 0.01:
                cur = s
            else:
                volt[k][i] = old
    return perms, volt


ATTEMPT_SECONDS = 3.0


def _lift_search(d, D, lo, hi, deadline, rng, consider):
    fails = 0
    n = lo + (lo % 2)
    while n <= hi and time.monotonic() < deadline and fails < 2:
        opts = []
        for b in range(1, n // 2 + 1):
            if n % (2 * b) != 0:
                continue
            m = n // (2 * b)
            if m < 3:
                continue
            if b == 1 and m > 2 * d * d:
                continue
            opts.append(b)
        if not opts:
            n += 2
            continue
        opts.sort(key=lambda b: abs(b - 4))
        ok = False
        for b in opts[:3]:
            if time.monotonic() >= deadline:
                break
            m = n // (2 * b)
            until = min(deadline, time.monotonic() + ATTEMPT_SECONDS)
            res = _try_lift(b, m, d, D, until, rng)
            if res is None:
                continue
            perms, volt = res
            darts = [(i, b + perms[k][i], volt[k][i])
                     for k in range(d) for i in range(b)]
            nn, edges = lib.voltage_lift(2 * b, darts, m)
            if consider(nn, edges):
                ok = True
                break
        fails = 0 if ok else fails + 1
        n += 2


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + max(1.0, min(0.80 * T, T - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    if D == 2:
        return best
    if d == 2:
        # Even cycle C_{2D}: bipartite, degree 2, diameter D.
        consider(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])
        return best

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    # Fallback bases from known structures (also seed the lift search).
    if D == 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
    if D == 4:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)]
        if qs:
            q = qs[0]
            try:
                n0, e0 = _gq_w(q)
                if q + 1 <= d:
                    e0 = _saturate(n0, e0, d, rng)
                consider(n0, e0)
            except Exception:
                pass

    if best[0] >= moore:
        return best

    # Bold search: random voltage lifts with hill climbing, sizes just above the fallback.
    if time.monotonic() < deadline:
        lo = best[0] + 2
        try:
            _lift_search(d, D, lo, moore, deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
