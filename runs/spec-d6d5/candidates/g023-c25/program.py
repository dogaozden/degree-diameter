import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families: projective plane, generalized quadrangle, arc
# extensions, and cover/saturation growth.
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
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
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
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
# Diameter repair by vertex deletion.
# ----------------------------------------------------------------------------

def _compact(n, edges, keep):
    """Relabel the kept vertices to 0..m-1 and keep only edges between them."""
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
# NEW: vectorised bi-Cayley eccentricity evaluator on a multiplication table.
#
# A group G of order m*k2 (semidirect Z_m x| Z_k2) is given by its full
# multiplication table M (numpy).  A bi-Cayley lift with k base vertices per
# side is a list of darts (i, j, s): A_{i,g} ~ B_{j, g*s} for all g in G.
#
# Left multiplication is an automorphism, so every vertex is in the orbit of
# some representative A_{i,e} or B_{j,e}.  The diameter is therefore at most D
# iff all 2k representatives reach every vertex within D steps.  All 2k
# breadth-first searches run at once as boolean numpy arrays, with no Python
# loop over vertices.  The table-lookup index arrays are precomputed once per
# group.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_sd(G, rng, k2_pool):
    """Random semidirect product Z_m x| Z_k2 of order G: returns (m, k2, r) or None."""
    for _ in range(60):
        k2 = rng.choice(k2_pool)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            return m, 1, 1
        cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if cands:
            return m, k2, rng.choice(cands)
    return None


def _group_table(m, k2, r):
    """Full multiplication table of Z_m x| Z_k2 (element (a, b) coded as a*k2 + b)."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    P = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    res_a = (a[:, None] + P[b][:, None] * a[None, :]) % m
    res_b = (b[:, None] + b[None, :]) % k2
    return res_a * k2 + res_b


def _inverse_index(M):
    """inv[g] = index of g^{-1}; identity is element 0."""
    G = M.shape[0]
    inv = np.empty(G, dtype=np.int64)
    rows, cols = np.nonzero(M == 0)
    inv[rows] = cols
    return inv


def _ecost(k, G, D, darts, IAB, IBA):
    """Total number of (representative, vertex) pairs not reached within D steps. Zero means valid.

    IAB[s] is the gather index for A -> B across dart s; IBA[s] for B -> A.
    """
    if len(set(darts)) < len(darts):
        return _BIG
    R = 2 * k
    VA = np.zeros((R, k, G), dtype=bool)
    VB = np.zeros((R, k, G), dtype=bool)
    for r in range(k):
        VA[r, r, 0] = True
        VB[k + r, r, 0] = True
    FA = VA.copy()
    FB = VB.copy()
    for _ in range(D):
        nA = np.zeros_like(VA)
        nB = np.zeros_like(VB)
        for i, j, s in darts:
            nB[:, j, :] |= FA[:, i, IAB[s]]
            nA[:, i, :] |= FB[:, j, IBA[s]]
        nA &= ~VA
        nB &= ~VB
        VA |= nA
        VB |= nB
        FA, FB = nA, nB
        if not (FA.any() or FB.any()):
            break
    return R * 2 * k * G - int(VA.sum()) - int(VB.sum())


def _random_darts(d, k, G, rng):
    """Layered darts: each of d layers is a permutation i -> p[i], with a random voltage."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append((i, p[i], rng.randrange(G)))
    return darts


def _anneal(d, D, k, G, IAB, IBA, rng, deadline, iters):
    """Annealing over voltages and layer permutations. Returns (darts_or_None, cost, darts)."""
    darts = _random_darts(d, k, G, rng)
    cost = _ecost(k, G, D, darts, IAB, IBA)
    T = 1.0
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.998)
        limit = cost - T * math.log(1.0 - rng.random())
        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            i, j, s = darts[idx]
            ns = rng.randrange(G)
            if ns == s:
                continue
            darts[idx] = (i, j, ns)
            c2 = _ecost(k, G, D, darts, IAB, IBA)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx] = (i, j, s)
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            old_a, old_b = darts[ia], darts[ib]
            darts[ia] = (old_a[0], old_b[1], old_a[2])
            darts[ib] = (old_b[0], old_a[1], old_b[2])
            c2 = _ecost(k, G, D, darts, IAB, IBA)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia] = old_a
                darts[ib] = old_b
    return (darts if cost == 0 else None), cost, darts


def _lift_edges(k, G, M, darts):
    """Full edge list of the lift: A_{i,g} = i*G+g, B_{j,h} = (k+j)*G+h."""
    E = set()
    for i, j, s in darts:
        col = M[:, s].tolist()
        for g in range(G):
            E.add((i * G + g, (k + j) * G + col[g]))
    return 2 * k * G, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

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
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.1 * time_limit, rng)
            consider(n2, e2)
        for n_c, e_c in _arc_extensions(d, start + 0.2 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.25 * time_limit, rng)
            consider(n2, e2)

    # Main search: bi-Cayley lifts over semidirect products (k = 1 covers Haar graphs),
    # annealed with the numpy evaluator, with vertex-deletion repair of near misses.
    ks = [1, 1, 1, 2, 3] if D >= 5 else [1, 1, 2, 3]
    k2_pool = [1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12]

    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        lo = max(2, base + 1)
        if k == 1:
            hi = lo + max(3, lo // 4)
        else:
            hi = lo + max(3, lo // 8)
        G = rng.randint(lo, hi)

        sd = _sample_sd(G, rng, k2_pool)
        if sd is None:
            continue
        m, k2, r = sd
        M = _group_table(m, k2, r)
        inv = _inverse_index(M)
        IAB = M[:, inv].T.copy()   # row s: gather index for A -> B across dart s
        IBA = M.T.copy()           # row s: gather index for B -> A across dart s

        iters = 3000 if k == 1 else 2000
        ok, c, darts = _anneal(d, D, k, G, IAB, IBA, rng, deadline, iters)
        if ok is not None:
            N, E = _lift_edges(k, G, M, ok)
            consider(N, E)
            continue

        if c <= 80 and rng.random() < 0.3 and time.monotonic() < deadline:
            N, E = _lift_edges(k, G, M, darts)
            rep_deadline = min(deadline, time.monotonic() + 3.0)
            rep = _repair(N, E, D, rep_deadline, rng)
            if rep is not None:
                n3, e3 = rep
                e3 = _saturate_edges(n3, e3, d, rng)
                consider(n3, e3)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
