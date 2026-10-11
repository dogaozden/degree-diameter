import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Projective-plane bases and arc extensions (diameter 3).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy point set with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Candidate (n, edges) graphs, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Cover-based vertex extension and edge saturation (diameter-preserving growth).
# ----------------------------------------------------------------------------

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
    """Extend by cover vertices, then saturate edges with the leftover degree."""
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
# NEW helper: group multiplication tables and vectorized lift cost.
#
# The semidirect product Z_m x|_r Z_k is tabulated once as a G x G numpy array
# MT[x, y] = x*y (vectorized, same formula as lib.semidirect_group). The right
# permutation of a voltage s is then the column MT[:, s].
#
# The cost of a bi-Cayley lift is evaluated with one numpy boolean matrix
# R (representatives x vertices). Each BFS step is a single fancy-indexed
# OR over the neighbour table, so no Python-level BFS loops run per move.
# ----------------------------------------------------------------------------

def _semidirect_table(m, k, r):
    """Full multiplication table of Z_m x|_r Z_k, element (a, b) coded a*k+b."""
    G = m * k
    r %= m
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(G, dtype=np.int64)
    a, b = x // k, x % k
    A, Bb = a[:, None], b[:, None]
    C, Dd = a[None, :], b[None, :]
    return ((A + pw[Bb] * C) % m) * k + (Bb + Dd) % k


def _sample_group(G, rng):
    """Return (m, k2, r) with m * k2 = G for a random semidirect product, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
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
        return m, k2, r
    return None


def _nbr_table(k, G, d, I, J, P, Pinv):
    """Neighbour table (N, d) of the bi-Cayley lift. A rows first, then B rows.

    Dart t joins A_{I[t], g} to B_{J[t], P[t, g]}. Returns None if the layer
    structure is not d-regular.
    """
    A = np.empty((k * G, d), dtype=np.int64)
    B = np.empty((k * G, d), dtype=np.int64)
    for i in range(k):
        t = np.nonzero(I == i)[0]
        if len(t) != d:
            return None
        A[i * G:(i + 1) * G] = ((k + J[t]) * G)[None, :] + P[t].T
    for j in range(k):
        t = np.nonzero(J == j)[0]
        if len(t) != d:
            return None
        B[j * G:(j + 1) * G] = (I[t] * G)[None, :] + Pinv[t].T
    return np.vstack([A, B])


def _cost(k, G, d, D, I, J, S, MT):
    """Number of unreached (representative, vertex) pairs within distance D; 0 means valid."""
    T = len(S)
    if len(set(zip(I.tolist(), J.tolist(), S.tolist()))) < T:
        return _BIG
    P = MT[:, S].T
    Pinv = np.argsort(P, axis=1)
    nbr = _nbr_table(k, G, d, I, J, P, Pinv)
    if nbr is None:
        return _BIG
    N = nbr.shape[0]
    reps = np.array([i * G for i in range(k)] + [(k + j) * G for j in range(k)], dtype=np.int64)
    R = np.zeros((len(reps), N), dtype=bool)
    R[np.arange(len(reps)), reps] = True
    for _ in range(D):
        newR = R | R[:, nbr].any(axis=2)
        if np.array_equal(newR, R):
            break
        R = newR
    return int(R.size - R.sum())


def _lift_edges(k, G, d, I, J, S, MT):
    """Edge list of the lift for the given darts."""
    P = MT[:, S].T
    Pinv = np.argsort(P, axis=1)
    nbr = _nbr_table(k, G, d, I, J, P, Pinv)
    E = set()
    for a in range(k * G):
        for b in nbr[a]:
            E.add((a, int(b)))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, MT, rng, deadline, iters):
    """Metropolis annealing over voltages and per-layer B-assignments.

    A move with new cost c2 is accepted iff c2 <= cost - T*ln(u), u ~ U(0,1].
    Temperature decays geometrically from 1.0 to 0.05.
    """
    T = d * k
    I = np.tile(np.arange(k, dtype=np.int64), d)
    J = np.empty(T, dtype=np.int64)
    S = np.empty(T, dtype=np.int64)
    for L in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            J[L * k + i] = p[i]
            S[L * k + i] = rng.randrange(G)

    cost = _cost(k, G, d, D, I, J, S, MT)
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        Temp = 1.0 * (0.05 ** (it / iters))
        u = 1.0 - rng.random()
        limit = cost - Temp * math.log(u)

        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(T)
            old = S[idx]
            new = rng.randrange(G)
            if new == old:
                continue
            S[idx] = new
            c2 = _cost(k, G, d, D, I, J, S, MT)
            if c2 <= limit:
                cost = c2
            else:
                S[idx] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            J[ia], J[ib] = J[ib], J[ia]
            c2 = _cost(k, G, d, D, I, J, S, MT)
            if c2 <= limit:
                cost = c2
            else:
                J[ia], J[ib] = J[ib], J[ia]

    if cost != 0:
        return None
    return _lift_edges(k, G, d, I, J, S, MT)


# ----------------------------------------------------------------------------
# Haar graph hill-climb (small D, secondary family).
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m for diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
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
# Driver.
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
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.2 * time_limit, rng)
            consider(n2, e2)
        for n_c, e_c in _arc_extensions(d, start + 0.3 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    # Main search: annealed bi-Cayley lifts over semidirect products.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    haar_m, haar_miss = d + 1, 0
    while time.monotonic() < deadline:
        if D <= 4 and haar_miss < 4 and rng.random() < 0.1:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
            continue

        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        m, k2, r = g
        order = m * k2
        MT = _semidirect_table(m, k2, r)
        res = _anneal(d, D, k, order, MT, rng, deadline, iters=3000)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
