import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from the parent).
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


def _two_color(n, edges):
    """Return a proper 2-colouring (list of 0/1) of the graph, or None if it is not bipartite."""
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


def _extend(n, edges, d, D, rng, deadline, max_fail=300):
    """Greedy pair insertion: repeatedly grow the order by 2 while the result stays valid."""
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    fails = 0
    while time.monotonic() < deadline and fails < max_fail:
        order = list(range(len(edges)))
        rng.shuffle(order)
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


# ----------------------------------------------------------------------------
# New search: bi-Cayley lifts over semidirect products Z_m x|_r Z_k2.
#
# Vertices: A_{i,g} = i*G + g, B_{p,h} = (k+p)*G + h, with |G| = G.
# Layer l joins A_i to B_{layers[l][i]} via voltage s: A_{i,g} ~ B_{p, g*s}.
# Each layer is a perfect matching between A-blocks and B-blocks, so the graph
# is d-regular and bipartite by construction.
#
# Because left multiplication by G is an automorphism acting regularly on each
# block, the diameter condition reduces to: every block root A_{i,1}, B_{p,1}
# reaches all N vertices within D steps. Each cost evaluation therefore runs
# 2k short BFS sweeps from the roots, which is much cheaper than a full
# all-pairs bitmask pass. The group order is searched by bisection per base
# size k, over many group families (not just the semidirect ones sampled before).
# ----------------------------------------------------------------------------

_PEN = 1000
_KS_WEIGHTS = [1, 1, 1, 2, 2, 3, 4]
_OPT_CACHE = {}


def _divisors(n):
    out = []
    for x in range(1, math.isqrt(n) + 1):
        if n % x == 0:
            out.append(x)
            if x * x != n:
                out.append(n // x)
    return sorted(out)


def _group_options(G):
    """List of (m, k2, rs) with m*k2 == G: Z_m x|_r Z_k2 for each admissible r in rs."""
    if G in _OPT_CACHE:
        return _OPT_CACHE[G]
    opts = []
    for k2 in _divisors(G):
        m = G // k2
        rs = [r for r in range(m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if rs:
            opts.append((m, k2, rs))
    _OPT_CACHE[G] = opts
    return opts


def _tables(m, k2, r):
    """Return (G, M, Inv): M[g, s] = g*s and Inv[s, h] = the g with g*s = h.

    Element (a, b) is coded a*k2 + b with (a,b)(c,e) = (a + r^b c, b + e).
    """
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Inv = np.empty((G, G), dtype=np.int64)
    ar = np.arange(G, dtype=np.int64)
    for s in range(G):
        Inv[s, M[:, s]] = ar
    return G, M, Inv


def _search(d, D, k, G, M, Inv, rng, deadline, iters):
    """Simulated annealing over voltages and layer permutations. Returns (n, edges) or None."""
    N = 2 * k * G
    roots = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)

    def set_layer(l):
        perm = layers[l]
        for i in range(k):
            p = perm[i]
            s = S[l][i]
            nbr[l, i * G:(i + 1) * G] = (k + p) * G + M[:, s]
            nbr[l, (k + p) * G:(k + p + 1) * G] = i * G + Inv[s]

    def dup():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    def unreached():
        total = 0
        for rt in roots:
            vis = np.zeros(N, dtype=bool)
            vis[rt] = True
            front = np.array([rt], dtype=np.int64)
            for _ in range(D):
                nb = nbr[:, front].ravel()
                nb = np.unique(nb[~vis[nb]])
                if nb.size == 0:
                    break
                vis[nb] = True
                front = nb
            total += N - int(np.count_nonzero(vis))
        return total

    def full_cost():
        return unreached() + _PEN * dup()

    for l in range(d):
        set_layer(l)
    cost = full_cost()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.3, 0.03 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)
        if k >= 2 and rng.random() < 0.3:
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            set_layer(l)
            c2 = full_cost()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                set_layer(l)
        else:
            i = rng.randrange(k)
            old = S[l][i]
            new = rng.randrange(G)
            if new == old:
                continue
            S[l][i] = new
            set_layer(l)
            c2 = full_cost()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                S[l][i] = old
                set_layer(l)

    if cost != 0:
        return None
    A = np.arange(k * G, dtype=np.int64)
    us = np.repeat(A, d)
    vs = nbr[:, :k * G].T.ravel()
    edges = list(zip(us.tolist(), vs.tolist()))
    return N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    search_deadline = start + 0.82 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n2, e2 = lib.haar_graph(D, [0, 1])  # cycle C_{2D}, diameter D
        if lib.is_valid(n2, e2, d, D):
            return n2, e2

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (calibration-style cases return immediately).
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

    if d >= 3 and D >= 3:
        moore = lib.moore_bound(d, D)
        KS = (1, 2, 3, 4)
        lo = {k: 1 for k in KS}
        hi = {k: moore // (2 * k) + 1 for k in KS}
        try:
            while time.monotonic() < search_deadline:
                for k in KS:
                    lo[k] = max(lo[k], best_n // (2 * k))
                k = rng.choice(_KS_WEIGHTS)
                if lo[k] + 1 >= hi[k]:
                    # Bisection converged: re-open the upper end to keep exploring.
                    hi[k] = min(moore // (2 * k) + 1, lo[k] + max(2, lo[k] // 12))
                    if lo[k] + 1 >= hi[k]:
                        continue
                G = (lo[k] + hi[k]) // 2
                if G <= lo[k]:
                    G = lo[k] + 1
                opts = _group_options(G)
                if not opts:
                    hi[k] = G
                    continue
                m, k2, rs = opts[rng.randrange(len(opts))]
                r = rs[rng.randrange(len(rs))]
                Gg, M, Inv = _tables(m, k2, r)
                slice_end = min(search_deadline, time.monotonic() + 3.0)
                res = _search(d, D, k, Gg, M, Inv, rng, slice_end, 6000)
                if res is not None:
                    lo[k] = G
                    consider(res[0], res[1])
                else:
                    hi[k] = G
        except Exception:
            pass

    try:
        n2, e2 = _extend(best_n, best[1], d, D, rng, deadline)
        if n2 > best_n:
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
