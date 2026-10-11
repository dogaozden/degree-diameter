"""Bi-Cayley (group-lift) search for D = 5, plus projective-plane and cover-growth baselines.

New family for D = 5: for a finite group G of order N and a connection set S of size d,
the bipartite graph with vertices (A, g) and (B, g), and edges (A, g) -- (B, g*s) for s in S,
is d-regular on 2N vertices. Its distances are governed by the sets W = S S^-1 and
W' = S^-1 S: the graph has diameter <= 5 when W*W = G and W'*W' = G. Searching S by
simulated annealing over many groups (cyclic, abelian, and semidirect products) is much
cheaper than checking the graph directly. Every candidate is still verified with lib.is_valid.
"""
import math
import random
import time
import itertools

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Projective-plane baseline and cover growth (safe fallbacks for other D).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1."""
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
    """Greedily join deficient opposite-side vertices in random order (only adds edges)."""
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
    """Extend by cover vertices, then saturate edges with the leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(6):
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
# Bi-Cayley graphs over finite groups, searched for diameter 5.
# ----------------------------------------------------------------------------

def _table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k (element (a, b) coded a*k + b; identity coded 0).

    Product: (a, b) * (c, d) = (a + r^b c, b + d), matching lib.semidirect_group.
    """
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    first = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    second = (b[:, None] + b[None, :]) % k
    return first * k + second


def _groups_of_order(N, rng, kmax=12):
    """Candidate (m, k, r) with m*k = N: cyclic, direct (r = 1), and a few semidirect products."""
    out = []
    for k in range(1, min(kmax, N) + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        if k == 1:
            out.append((m, 1, 1))
            continue
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        out.append((m, k, 1))
        rng.shuffle(rs)
        for r in rs[:3]:
            out.append((m, k, r))
    rng.shuffle(out)
    return out


def _anneal(T, inv, N, d, rng, end, iters):
    """Search S (|S| = d) with W*W = G and W'*W' = G, where W = S S^-1 and W' = S^-1 S.

    Returns S when the cost is zero, otherwise None.
    """
    def cost(S):
        Sa = np.array(S, dtype=np.int64)
        iS = inv[Sa]
        W = np.unique(T[np.ix_(Sa, iS)])
        W2 = np.unique(T[np.ix_(W, W)])
        P = np.unique(T[np.ix_(iS, Sa)])
        P2 = np.unique(T[np.ix_(P, P)])
        return (N - len(W2)) + (N - len(P2))

    S = rng.sample(range(N), d)
    c = cost(S)
    for it in range(iters):
        if c == 0:
            return S
        if (it & 63) == 0 and time.monotonic() >= end:
            break
        temp = 1.0 * (1.0 - it / iters) + 0.05
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        new = S[:]
        new[i] = x
        c2 = cost(new)
        if c2 <= c or rng.random() < math.exp((c - c2) / temp):
            S, c = new, c2
    return S if c == 0 else None


def _attempt(N, d, rng, end):
    """Try several groups of order N. Returns (T, S) on success, otherwise None."""
    for m, k, r in _groups_of_order(N, rng)[:6]:
        if time.monotonic() >= end:
            break
        T = _table(m, k, r)
        inv = (T == 0).argmax(axis=1)
        S = _anneal(T, inv, N, d, rng, end, 4000)
        if S is not None:
            return T, S
    return None


def _bicayley_edges(T, S, N):
    """Edges of the bi-Cayley graph: A-vertex g joins B-vertex N + T[g, s] for s in S."""
    arr = T[:, S].tolist()
    return [(g, N + h) for g, row in enumerate(arr) for h in row]


def _bicayley_search(d, rng, deadline, consider, start_order):
    """Climb group orders above the best valid one, verifying each success."""
    best_order = max(start_order, d)
    rr = 0
    while time.monotonic() < deadline:
        N = best_order + 1 + (rr % 4)
        rr += 1
        end = min(deadline, time.monotonic() + 2.5)
        res = _attempt(N, d, rng, end)
        if res is None:
            continue
        T, S = res
        n, e = 2 * N, _bicayley_edges(T, S, N)
        if consider(n, e):
            best_order = N


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        valid = lib.is_valid(n, e, d, D)
        if valid and n > best_n:
            best = (n, e)
            best_n = n
        return valid

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.1 * time_limit, rng)
            consider(n2, e2)

    if D == 5 and d >= 2:
        _bicayley_search(d, rng, deadline, consider, best_n // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
