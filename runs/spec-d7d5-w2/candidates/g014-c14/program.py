import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe exact families (kept from the parent for calibration and fallback).
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
# NEW construction: single-block bi-Cayley graphs (vertex-transitive on each side).
#
# Group G = Z_m x| Z_k2 (order G). Vertices A_g and B_h, g, h in G.
# Edges: A_g ~ B_{g*s} for s in a set S of d distinct group elements.
# Left multiplication by x is an automorphism, so the whole diameter check
# reduces to two breadth-first searches, from A_e and from B_e.
# Search: simulated annealing over the d-element set S, minimising the number
# of vertices unreached within distance D from the two sources.
# Order is grown exponentially, then refined by search. Each success is
# verified by lib.is_valid before it is accepted.
# ----------------------------------------------------------------------------

def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h.
    """
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _group_options(G, rng, cap=8):
    """List of (m, k2, r) with m * k2 = G giving semidirect products Z_m x| Z_k2."""
    opts = []
    for k2 in range(1, min(G, 40) + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            opts.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        rng.shuffle(rs)
        opts.extend((m, k2, r) for r in rs[:cap])
    rng.shuffle(opts)
    return opts


def _sa(d, D, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over the connection set S (size d). Returns S or None."""
    N = 2 * G
    S = rng.sample(range(G), d)

    def cost(S):
        idx = np.array(S, dtype=np.int64)
        NB = np.vstack([G + Ts[idx].T, Invs[idx].T])  # rows 0..G-1: A, rows G..2G-1: B
        total = 0
        for src in (0, G):
            seen = np.zeros(N, dtype=bool)
            seen[src] = True
            front = np.array([src], dtype=np.int64)
            for _ in range(D):
                new = np.zeros(N, dtype=bool)
                new[NB[front].ravel()] = True
                new &= ~seen
                if not new.any():
                    break
                seen |= new
                front = np.flatnonzero(new)
            total += N - int(np.count_nonzero(seen))
        return total

    c = cost(S)
    for t in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        x = rng.randrange(G)
        if x in S:
            continue
        j = rng.randrange(d)
        old = S[j]
        S[j] = x
        c2 = cost(S)
        temp = max(0.3, 2.0 * (1.0 - t / iters))
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            c = c2
        else:
            S[j] = old
    return list(S) if c == 0 else None


def _attempt(d, D, G, rng, slice_end):
    """Try to find a valid single-block bi-Cayley graph with base order G before slice_end."""
    opts = _group_options(G, rng)
    i = 0
    while opts and time.monotonic() < slice_end:
        m, k2, r = opts[i % len(opts)]
        i += 1
        _, Ts, Invs = _semidirect_tables(m, k2, r)
        S = _sa(d, D, G, Ts, Invs, rng, slice_end, 3000)
        if S is not None:
            edges = [(g, G + int(Ts[s, g])) for s in S for g in range(G)]
            return 2 * G, edges
    return None


# ----------------------------------------------------------------------------
# Greedy pair insertion (kept from the parent): grows the order by 2 per step.
# ----------------------------------------------------------------------------

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


def _extend(n, edges, d, D, rng, deadline):
    """Greedy pair insertion: repeatedly grow the order by 2 while the result stays valid."""
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    while time.monotonic() < deadline:
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
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    search_deadline = start + 0.85 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # New search: exponential then refined search over the base order G (total 2G).
    moore_half = lib.moore_bound(d, D) // 2
    G = max(d, best_n // 2 + 1)
    lo = None
    step = 1
    slice_len = max(2.0, min(6.0, 0.12 * budget))
    while time.monotonic() < search_deadline:
        if G > moore_half:
            break
        res = _attempt(d, D, G, rng, min(search_deadline, time.monotonic() + slice_len))
        if res is not None:
            consider(res[0], res[1])
            lo = G
            step = max(1, step * 2)
            G = G + step
        else:
            if lo is None:
                step = 1
                G = max(d, G - max(1, G // 10))
            else:
                step = max(1, step // 2)
                G = lo + step

    # Greedy pair insertion on the best graph found so far.
    try:
        n2, e2 = _extend(best_n, best[1], d, D, rng, deadline)
        if n2 > best_n:
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
