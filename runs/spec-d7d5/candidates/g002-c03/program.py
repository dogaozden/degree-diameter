import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Projective-plane base (D >= 3) and cover-based growth.
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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of the graph."""
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
            for attempt in range(200):
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
    """Greedily join deficient opposite-side vertices in random order."""
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
    """Extend by cover vertices first, then saturate edges with the leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2, searched with numpy.
#
# Layers: for each layer L (d of them) a permutation P[L] of the k base
# vertices on each side, and a voltage V[L][i] in the group. Dart (L, i)
# joins A_{i,g} to B_{P[L][i], g * V[L][i]} for every g in the group.
# Each A and each B vertex then has degree exactly d. Vertex-transitivity
# inside fibres reduces the diameter check to 2k BFS sources.
# ----------------------------------------------------------------------------

class _Group:
    """Semidirect product Z_m x| Z_k2 with element (a, b) coded as a*k2 + b."""

    def __init__(self, m, k2, r):
        self.m = m
        self.k2 = k2
        self.G = m * k2
        idx = np.arange(self.G, dtype=np.int64)
        self.A = idx // k2
        self.B = idx % k2
        pw = np.array([pow(r, b, m) for b in range(k2)], dtype=np.int64)
        self.pw = pw[self.B]
        self.cache = {}

    def perm(self, s):
        """Return (g -> g*s as array, its inverse permutation), cached per voltage s."""
        hit = self.cache.get(s)
        if hit is None:
            c, dd = divmod(s, self.k2)
            pv = ((self.A + self.pw * c) % self.m) * self.k2 + (self.B + dd) % self.k2
            hit = (pv, np.argsort(pv))
            self.cache[s] = hit
        return hit


def _sample_group_exact(G, rng):
    """Random semidirect product of order exactly G (k2 <= 12); falls back to cyclic."""
    k2s = [x for x in range(1, min(G, 12) + 1) if G % x == 0 and G // x >= 2]
    k2 = rng.choice(k2s) if (k2s and rng.random() < 0.7) else 1
    if k2 == 1:
        return _Group(G, 1, 1)
    m = G // k2
    units = [r for r in range(1, m)
             if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
    if not units:
        return _Group(G, 1, 1)
    return _Group(m, k2, rng.choice(units))


def _build_nbr(grp, k, d, P, V):
    """Neighbour table of shape (2kG, d): every vertex has exactly one neighbour per layer."""
    G = grp.G
    nbr = np.empty((2 * k * G, d), dtype=np.int64)
    for L in range(d):
        for i in range(k):
            j = P[L][i]
            pv, inv = grp.perm(V[L][i])
            nbr[i * G:(i + 1) * G, L] = (k + j) * G + pv
            nbr[(k + j) * G:(k + j + 1) * G, L] = i * G + inv
    return nbr


def _cost_np(nbr, reps, N, D):
    """Number of (source, vertex) pairs not within distance D; zero means valid."""
    S = reps.shape[0]
    R = np.zeros((S, N), dtype=bool)
    R[np.arange(S), reps] = True
    for _ in range(D):
        R = R | R[:, nbr].any(axis=2)
    return S * N - int(R.sum())


def _keys_ok(P, V, k, d):
    """True if no two darts share (base i, base j, voltage) -- avoids multi-edges."""
    keys = set()
    for L in range(d):
        for i in range(k):
            keys.add((i, P[L][i], V[L][i]))
    return len(keys) == d * k


def _edges_from(nbr, k, G):
    """Edge list of the lift; A indices are all smaller than B indices."""
    edges = []
    for a in range(k * G):
        for b in nbr[a].tolist():
            edges.append((a, b))
    return 2 * k * G, edges


def _anneal(d, D, k, grp, rng, deadline, iters):
    """Simulated annealing over voltages and layer permutations; returns (n, edges) or None."""
    G = grp.G
    if k * G < d:
        return None
    N = 2 * k * G
    reps = np.array([i * G for i in range(k)] + [(k + j) * G for j in range(k)],
                    dtype=np.int64)

    P = V = None
    for _ in range(2000):
        P = []
        V = []
        for _ in range(d):
            p = list(range(k))
            rng.shuffle(p)
            P.append(p)
            V.append([rng.randrange(G) for _ in range(k)])
        if _keys_ok(P, V, k, d):
            break
    else:
        return None

    def cost_of(P, V):
        return _cost_np(_build_nbr(grp, k, d, P, V), reps, N, D)

    cost = cost_of(P, V)
    T0, T1 = 2.0, 0.2
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        L = rng.randrange(d)
        if k == 1 or rng.random() < 0.6:
            i = rng.randrange(k)
            old = V[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            V[L][i] = new
            saved = ("V", L, i, old)
        else:
            a, b = rng.sample(range(k), 2)
            P[L][a], P[L][b] = P[L][b], P[L][a]
            saved = ("P", L, a, b)
        if _keys_ok(P, V, k, d):
            c2 = cost_of(P, V)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
                continue
        # Reject: revert the move.
        if saved[0] == "V":
            V[saved[1]][saved[2]] = saved[3]
        else:
            _, L2, a2, b2 = saved
            P[L2][a2], P[L2][b2] = P[L2][b2], P[L2][a2]

    if cost != 0:
        return None
    return _edges_from(_build_nbr(grp, k, d, P, V), k, G)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = float(time_limit)
    search_end = start + 0.72 * total
    final_end = start + 0.84 * total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2, valid for every D >= 2).
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.15 * total, rng)
            consider(n2, e2)

    if D == 3:
        if time.monotonic() < final_end - 1.0 and best[0] > 2:
            n2, e2 = _grow(best[0], best[1], d, D, final_end, rng)
            consider(n2, e2)
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # D >= 4: annealed bi-Cayley lifts over semidirect products, with the group
    # order chosen just above the current best (record shape: 2 * k * G).
    ks = [1, 1, 1, 2, 2, 3, 4]
    while time.monotonic() < search_end:
        k = rng.choice(ks)
        G = best[0] // (2 * k) + rng.randrange(1, 6)
        grp = _sample_group_exact(G, rng)
        run_end = min(search_end, time.monotonic() + 0.08 * total)
        res = _anneal(d, D, k, grp, rng, run_end, 4000)
        if res is not None:
            consider(res[0], res[1])

    # Polish: spend remaining slack growing the best graph.
    if time.monotonic() < final_end - 1.0:
        n2, e2 = _grow(best[0], best[1], d, D, final_end, rng)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
