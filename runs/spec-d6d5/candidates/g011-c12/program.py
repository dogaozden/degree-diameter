import itertools
import math
import random
import time

import numpy as np

import lib


BIG = 10 ** 9
_REPAIR_MAX_COST = 60


# ----------------------------------------------------------------------------
# Projective-plane and arc-extension baselines.
# ----------------------------------------------------------------------------

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
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
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
# Generic graph helpers: balls, cover-extension, saturation, repair.
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
    return n, edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate with leftover degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)[1]
        if not grew:
            break
    return cur_n, cur_e


def _compact(n, edges, keep):
    """Relabel kept vertices to 0..m-1 and keep only edges between them."""
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    E = [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]
    return len(new), E


def _repair(n, edges, D, deadline, rng):
    """Delete far-off vertices in batches until diameter <= D. Returns (n, edges) or None."""
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


# ----------------------------------------------------------------------------
# NEW HELPER: group multiplication tables and batched bitset-style reach.
#
# Bi-Cayley lift over a finite group G (given by its multiplication table M):
#   vertices A_i,g = i*G + g and B_j,h = (k+j)*G + h,
#   dart (i, j, s) joins A_i,g to B_j,g*s.
# Left translations are automorphisms, so one source per layer (A_i,e and B_j,e)
# suffices for the diameter check. All 2k sources are propagated at once with
# numpy boolean arrays shaped (sources, layers, |G|) instead of Python BFS.
# ----------------------------------------------------------------------------

def _group_tables(m, k2, r):
    """Multiplication table M and inverse array of Z_m x| Z_k2 (element (a,b) coded a*k2+b)."""
    G = m * k2
    pw = np.array([pow(r, b, m) for b in range(k2)], dtype=np.int64)
    x = np.arange(G, dtype=np.int64)
    a, b = x // k2, x % k2
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    inv = np.argmax(M == 0, axis=1).astype(np.int64)
    return G, M, inv


def _sample_group(G, rng, k2_choices):
    """Random semidirect product Z_m x| Z_k2 of order G, as (order, M, inv), or None."""
    for _ in range(80):
        k2 = rng.choice(k2_choices)
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
        return _group_tables(m, k2, r)
    return None


def _cost_fast(k, G, M, inv, D, darts):
    """Total number of (source, vertex) pairs not reached within D. Zero means diameter <= D."""
    seen = set()
    for row in darts:
        t = (row[0], row[1], row[2])
        if t in seen:
            return BIG
        seen.add(t)
    arr = np.asarray(darts, dtype=np.int64)
    Ai, Bj, S = arr[:, 0], arr[:, 1], arr[:, 2]
    S0 = 2 * k
    T1 = M[:, S]        # (G, nd): g -> g*s
    T2 = M[:, inv[S]]   # (G, nd): h -> h*s^-1
    base = (np.arange(S0, dtype=np.int64) * (k * G))[:, None, None]
    flat_b = base + (Bj * G)[None, None, :] + T1[None, :, :]   # (S0, G, nd)
    flat_a = base + (Ai * G)[None, None, :] + T2[None, :, :]
    size = S0 * k * G

    F = np.zeros((S0, 2 * k, G), dtype=bool)
    idx = np.arange(S0)
    F[idx, idx, 0] = True
    V = F.copy()
    for _ in range(D):
        mA = np.transpose(F[:, :k, :][:, Ai, :], (0, 2, 1))   # from A-layers to B-layers
        mB = np.transpose(F[:, k:, :][:, Bj, :], (0, 2, 1))   # from B-layers to A-layers
        nb = np.zeros(size, dtype=bool)
        nb[flat_b[mA]] = True
        na = np.zeros(size, dtype=bool)
        na[flat_a[mB]] = True
        new = np.concatenate([na.reshape(S0, k, G), nb.reshape(S0, k, G)], axis=1)
        new &= ~V
        if not new.any():
            break
        V |= new
        F = new
    return S0 * (2 * k * G) - int(V.sum())


def _edges_fast(k, G, M, darts):
    """Full edge list of the lift: (n, edges)."""
    E = set()
    g = np.arange(G, dtype=np.int64)
    for i, j, s in darts:
        tgt = M[g, s]
        for x, y in zip((i * G + g).tolist(), ((k + j) * G + tgt).tolist()):
            E.add((x, y))
    return 2 * k * G, sorted(E)


def _accept(c2, cost, T, rng):
    if c2 <= cost:
        return True
    return rng.random() < math.exp(-(c2 - cost) / T)


def _anneal_fast(d, D, k, G, M, inv, rng, deadline, iters, start=None, T0=3.0, T1=0.2):
    """Annealing over voltages and per-layer B-assignments. Returns (darts, cost)."""
    if start is None:
        darts = []
        for _ in range(d):
            p = rng.sample(range(k), k)
            for i in range(k):
                darts.append([i, p[i], rng.randrange(G)])
    else:
        darts = [list(x) for x in start]
    nd = len(darts)
    cost = _cost_fast(k, G, M, inv, D, darts)
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(nd)
            old = darts[idx][2]
            darts[idx][2] = rng.randrange(G)
            c2 = _cost_fast(k, G, M, inv, D, darts)
            if _accept(c2, cost, T, rng):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost_fast(k, G, M, inv, D, darts)
            if _accept(c2, cost, T, rng):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts, cost


def _perturb(darts, G, rng, flips):
    """Copy of a dart assignment with `flips` random voltages re-rolled."""
    out = [list(x) for x in darts]
    for _ in range(flips):
        idx = rng.randrange(len(out))
        out[idx][2] = rng.randrange(G)
    return out


# ----------------------------------------------------------------------------
# Top level.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.15 * time_limit, rng)
            consider(n2, e2)
        if best_n < moore:
            for n_c, e_c in _arc_extensions(d, start + 0.2 * time_limit,
                                            random.Random(seed * 7919 + d)):
                consider(n_c, e_c)

    if best_n >= moore:
        return best

    # Main search: bi-Cayley lifts over Z_m x| Z_k2 with fast numpy evaluation,
    # elite warm restarts, and repair of near-miss lifts by vertex deletion.
    ks = [1, 1, 1, 2, 2, 3] if D >= 5 else [1, 1, 2, 3]
    k2_pool = [1, 2, 2, 3, 3, 4, 5, 6, 6, 7, 8, 9, 10, 11, 12]
    elite = {}
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        lo = best_n // (2 * k) + 1
        hi = lo + max(3, lo // 8)
        G = rng.randint(max(2, lo), hi)
        g = _sample_group(G, rng, k2_pool)
        if g is None:
            continue
        G, M, inv = g
        key = (k, G)

        start_darts, T0 = None, 3.0
        if key in elite and rng.random() < 0.5:
            _, st = elite[key]
            start_darts = _perturb(st, G, rng, rng.randint(1, 3))
            T0 = 1.0

        iters = 3000 if k == 1 else 1200
        darts, c = _anneal_fast(d, D, k, G, M, inv, rng, deadline, iters, start_darts, T0)
        if c == 0:
            n0, e0 = _edges_fast(k, G, M, darts)
            consider(n0, e0)
            continue

        if key not in elite or c < elite[key][0]:
            elite[key] = (c, darts)

        if c <= _REPAIR_MAX_COST and rng.random() < 0.35 and time.monotonic() < deadline:
            n0, e0 = _edges_fast(k, G, M, darts)
            rep_deadline = min(deadline, time.monotonic() + 4.0)
            rep = _repair(n0, e0, D, rep_deadline, rng)
            if rep is not None:
                n1, e1 = _saturate_edges(rep[0], rep[1], d, rng)
                consider(n1, e1)
                grow_deadline = min(deadline, time.monotonic() + 3.0)
                n3, e3 = _grow(n1, e1, d, D, grow_deadline, rng)
                consider(n3, e3)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
