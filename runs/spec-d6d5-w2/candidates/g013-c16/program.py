"""Targets d=6, D=5 by searching bi-Cayley graphs over a wider pool of groups.

Changes from the parent: for D >= 5 the time goes to a bi-Cayley search over
semidirect products Z_m x| Z_k and affine groups AGL(1,p), with orders chosen
just above the current record half-order. Each candidate is annealed on a
vectorised cost, then checked with lib.is_valid. The PG/Araujo-Lopez/Haar
phases and the K_{d,d} fallback stay in place, so every case still returns a
valid graph.
"""
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Generic graph helpers.
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


def _adj_from(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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


def _extend_cover(n, edges, d, D, deadline, rng, randomize=False):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = _adj_from(n, edges)
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
            for attempt in range(100):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng,
                                       randomize or attempt > 0)
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
    adj = _adj_from(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
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


def _grow(n, edges, d, D, deadline, rng, randomize=False):
    cur_n, cur_e = n, list(edges)
    for _ in range(6):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, randomize)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Base families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m for a Haar graph of diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0 or time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


# ----------------------------------------------------------------------------
# Bi-Cayley search (D >= 5).
#
# Vertices A_x = x and B_w = G + w. Edge A_x ~ B_{x*s} for s in S, |S| = d.
# Left multiplication is an automorphism, so validity reduces to BFS from
# A_1 and B_1 within D steps.
# ----------------------------------------------------------------------------

def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def _affine_mul(p):
    """AGL(1,p): element (u-1)*p + b encodes x -> u*x + b, with u in 1..p-1."""
    def mul(x, y):
        u, b = divmod(x, p)
        u += 1
        v, c = divmod(y, p)
        v += 1
        return (((u * v) % p) - 1) * p + (u * c + b) % p
    return mul


def _mul_table(order, mul):
    M = np.empty((order, order), dtype=np.int64)
    for x in range(order):
        M[x, :] = [mul(x, y) for y in range(order)]
    return M


def _identity_ok(M):
    G = M.shape[0]
    ar = np.arange(G)
    return bool(np.array_equal(M[0], ar) and np.array_equal(M[:, 0], ar))


def _sample_group(G, rng):
    """Return (order, mul) for a group of order G: AGL(1,p) if G = p(p-1), else Z_m x| Z_k."""
    p = None
    for cand in range(3, G + 2):
        if cand * (cand - 1) == G and _is_prime(cand):
            p = cand
            break
    if p is not None and rng.random() < 0.5:
        return G, _affine_mul(p)
    ks = [k for k in range(1, 13) if G % k == 0 and G // k >= 2]
    rng.shuffle(ks)
    for k in ks:
        m = G // k
        cands = [1]
        if k > 1 and m > 2:
            tries = rng.sample(range(2, m), min(m - 2, 80))
            cands += [r for r in tries if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        return order, mul
    return None


def _bc_adj(M, inv, S, G):
    Sa = np.asarray(S, dtype=np.int64)
    return np.vstack([G + M[:, Sa], M[:, inv[Sa]]])


def _bc_cost(adj, G, D):
    """Unreached vertices from A_1 (node 0) and B_1 (node G) within D steps. Zero means valid."""
    N = adj.shape[0]
    total = 0
    for src in (0, G):
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = adj[frontier].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            frontier = nb
        total += N - int(np.count_nonzero(seen))
    return total


def _anneal_S(M, inv, G, d, D, deadline, rng, iters):
    S = rng.sample(range(G), d)
    c = _bc_cost(_bc_adj(M, inv, S, G), G, D)
    T = 1.5
    for _ in range(iters):
        if c == 0 or time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T2 = S[:]
        T2[i] = x
        c2 = _bc_cost(_bc_adj(M, inv, T2, G), G, D)
        if c2 <= c or rng.random() < math.exp((c - c2) / T):
            S, c = T2, c2
        T = max(0.05, T * 0.997)
    return S if c == 0 else None


def _bc_edges(M, S, G):
    E = [(x, G + int(M[x, s])) for x in range(G) for s in S]
    return 2 * G, E


# ----------------------------------------------------------------------------
# Main build.
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
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.08 * time_limit, rng)
            consider(n2, e2)
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 5 and d >= 3:
        bc_rng = random.Random(seed * 1000003 + d * 131 + D)
        half_moore = moore // 2
        while time.monotonic() < deadline - 0.5:
            lo = max(2 * d, best_n // 2 + 1, int(0.38 * half_moore))
            G = bc_rng.randint(lo, lo + max(4, lo // 4))
            g = _sample_group(G, bc_rng)
            if g is None:
                continue
            order, mul = g
            M = _mul_table(order, mul)
            if not _identity_ok(M):
                continue
            inv = np.argmax(M == 0, axis=1)
            sub = min(deadline, time.monotonic() + 8.0)
            S = _anneal_S(M, inv, order, d, D, sub, bc_rng, 3000)
            if S is not None:
                n, e = _bc_edges(M, S, order)
                consider(n, e)
    elif D >= 3 and d >= 3:
        haar_m = d + 1
        misses = 0
        while time.monotonic() < deadline - 0.5 and misses < 6 and haar_m <= 80:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                misses = 0
            else:
                misses += 1
            haar_m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
