import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline: projective plane incidence graphs (valid for D >= 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley (Haar-type) graphs over non-abelian groups.
#
# Group G = Z_m x| Z_k (order G). Vertices (0,g) and (1,x), g, x in G.
# Edges (0,g)-(1,g*s) for s in S, |S| = d. Left multiplication is an
# automorphism, so diameter <= D iff BFS from (0,e) and from (1,e) reach
# everything within D steps. The cost is the number of unreached pairs.
# ----------------------------------------------------------------------------

def _cost(P, Pi, G, D):
    """Unreached (source, vertex) pairs over the two sources (0,e) and (1,e). Zero iff diameter <= D.

    P[t][g] = g * s_t (side 0 -> side 1), Pi[t][x] = x * s_t^{-1} (side 1 -> side 0).
    """
    total = 0
    for src in (0, 1):
        seen = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
        seen[src][0] = True          # identity has code 0
        f = np.array([0], dtype=np.int64)
        cur = src
        for _ in range(D):
            if f.size == 0:
                break
            nb = (P if cur == 0 else Pi)[:, f].ravel()
            oth = 1 - cur
            mask = np.zeros(G, dtype=bool)
            mask[nb] = True
            mask &= ~seen[oth]
            seen[oth] |= mask
            f = np.flatnonzero(mask)
            cur = oth
        total += 2 * G - int(seen[0].sum()) - int(seen[1].sum())
    return total


def _pick_group(G, rng):
    """Random (m, k, r) with m * k = G and Z_m x| Z_k nonabelian (r != 1) most of the time."""
    for _ in range(40):
        if rng.random() < 0.9:
            ks = [k for k in range(2, 13) if G % k == 0]
        else:
            ks = [1]
        if not ks:
            continue
        k = rng.choice(ks)
        m = G // k
        if m < 2:
            continue
        if k == 1:
            return m, 1, 1
        cands = [r for r in range(2, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not cands:
            continue
        return m, k, rng.choice(cands)
    return None


def _anneal_haar(d, D, G, mul, inv, rng, deadline, iters):
    """Anneal a connection set S (|S| = d, s != identity) in the group. Returns (cost, S, cache)."""
    cache = {}

    def rows(s):
        if s not in cache:
            P = np.array([mul(g, s) for g in range(G)], dtype=np.int64)
            si = inv(s)
            Pi = np.array([mul(g, si) for g in range(G)], dtype=np.int64)
            cache[s] = (P, Pi)
        return cache[s]

    def eval_cost(S):
        rs = [rows(s) for s in S]
        P = np.stack([r[0] for r in rs])
        Pi = np.stack([r[1] for r in rs])
        return _cost(P, Pi, G, D)

    S = rng.sample(range(1, G), d)
    cost = eval_cost(S)
    T = 2.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        s_new = rng.randrange(1, G)
        if s_new in S:
            continue
        S2 = S[:]
        S2[i] = s_new
        c2 = eval_cost(S2)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            S, cost = S2, c2
        T = max(0.2, T * 0.997)
    return cost, S, cache


def _haar_edges(G, S, cache):
    """Edges of the bi-Cayley graph on 2G vertices (side 0 is 0..G-1, side 1 is G..2G-1)."""
    E = []
    for s in S:
        P = cache[s][0]
        for g in range(G):
            E.append((g, G + int(P[g])))
    return 2 * G, E


# ----------------------------------------------------------------------------
# Diameter repair by vertex deletion, then saturation (only adds edges).
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


def _compact(n, edges, keep):
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    E = [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]
    return len(new), E


def _repair(n, edges, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        if cur_n == 0:
            return None
        adj = [[] for _ in range(cur_n)]
        for u, v in cur_e:
            adj[u].append(v)
            adj[v].append(u)
        ball = _balls_radius(cur_n, adj, D)
        bad = [cur_n - b.bit_count() for b in ball]
        if not any(bad):
            return cur_n, cur_e
        bad_v = [v for v in range(cur_n) if bad[v] > 0]
        rng.shuffle(bad_v)
        bad_v.sort(key=lambda v: -bad[v])
        batch = max(1, len(bad_v) // 12)
        dead = set(bad_v[:batch])
        keep = [v not in dead for v in range(cur_n)]
        cur_n, cur_e = _compact(cur_n, cur_e, keep)
    return None


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
    """Greedily join deficient opposite-side vertices (only adds edges, so diameter cannot grow)."""
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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return n, edges


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            # For D = 3 with d-1 a prime power, PG(2, d-1) meets the Moore bound.
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    moore_n = lib._moore_bound(d, D)
    if best_n >= moore_n:
        return best

    # Bi-Cayley search over non-abelian groups for the target band.
    moore_side = moore_n // 2
    target = max(best_side_init := best_n // 2 + 1, int(0.44 * moore_side))
    fails = 0
    while time.monotonic() < deadline:
        best_side = best_n // 2
        target = max(target, best_side + 1)
        lo = target
        G = rng.randint(lo, lo + 6)
        if G <= d + 1:
            continue
        g = _pick_group(G, rng)
        if g is None:
            fails += 1
            continue
        m, k, r = g
        try:
            order, mul, inv = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        if order != G:
            continue

        cost, S, cache = _anneal_haar(d, D, G, mul, inv, rng, deadline, 1200)
        if cost == 0:
            n, e = _haar_edges(G, S, cache)
            consider(n, e)
            fails = 0
            continue

        fails += 1
        if fails > 40:
            # Lower the target gently if nothing in the band works.
            target = max(best_side + 1, int(target * 0.99))
            fails = 0

        # Near miss: build the full lift, delete far-off vertices, saturate.
        if cost <= 25 and rng.random() < 0.5 and time.monotonic() < deadline:
            n, e = _haar_edges(G, S, cache)
            rep_deadline = min(deadline, time.monotonic() + 3.0)
            rep = _repair(n, e, D, rep_deadline, rng)
            if rep is not None:
                n2, e2 = _saturate(rep[0], rep[1], d, rng)
                consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
