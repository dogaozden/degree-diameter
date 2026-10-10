import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000          # hard cap on vertex count (keeps is_valid fast and memory small)
ITERS = 3000          # annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side
GROW_PAIRS = 12       # maximum number of new vertex pairs the growth step may add


def _neighbors(P, Pinv, V, s, m):
    """Neighbour table (n x d) of the Z_m lift of a d-regular bipartite base on s+s vertices.

    Dart k joins A-vertex i to B-vertex P[k, i] with voltage V[k, i]. A-lift id = i*m+g,
    B-lift id = (s+j)*m+h. Every lift vertex gets exactly one neighbour per dart.
    """
    d = P.shape[0]
    g = np.arange(m, dtype=np.int64)
    nbr = np.empty((2 * s * m, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            nbr[i * m:(i + 1) * m, k] = s * m + j * m + (g + int(V[k, i])) % m
        for j in range(s):
            i = int(Pinv[k, j])
            nbr[(s + j) * m:(s + j + 1) * m, k] = i * m + (g - int(V[k, i])) % m
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid.

    The Z_m action is transitive on each fibre, so checking the base-vertex sources suffices.
    """
    n = nbr.shape[0]
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        M = R.copy()
        for k in range(nbr.shape[1]):
            M |= R[:, nbr[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    return int(S * n - np.count_nonzero(R))


def _swap(P, Pinv, k, a, b):
    P[k, a], P[k, b] = P[k, b], P[k, a]
    Pinv[k, P[k, a]] = a
    Pinv[k, P[k, b]] = b


def _anneal(s, m, d, D, rng, deadline):
    """Simulated annealing over permutations and voltages. Returns (P, V) with zero cost, or None."""
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(m) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * m for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, m)
    cur = _cost(nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(d), rng.randrange(s)
            old = int(V[k, i])
            new_v = rng.randrange(m)
            if new_v == old:
                continue
            V[k, i] = new_v
            cand = _neighbors(P, Pinv, V, s, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)  # swapping the same positions again undoes it
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph(s, m, P, V, d):
    """Materialise the lift as (n, edges), deduplicated."""
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, m)
    edges = set()
    for x in range(s * m):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * m, sorted(edges)


def _search(s, d, D, rng, deadline, cap):
    """For fixed s, find the largest m (by doubling then bisection) whose lift passes annealing."""
    best = None
    lo, hi = 0, None
    m = 1
    while time.monotonic() < deadline:
        if 2 * s * m > cap:
            hi = m
        else:
            st = _anneal(s, m, d, D, rng, deadline)
            if st is not None:
                lo = m
                best = (m, st[0], st[1])
            else:
                hi = m
        if hi is None:
            m = 2 * lo
        else:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2
    return best


def _largest_prime_power(k):
    """Largest prime power q with 2 <= q <= k, or None."""
    for q in range(k, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _spare_augment(n, edges, d, seed):
    """Add point-line edges (between non-incident pairs) using spare degree.

    Works for a bipartite graph whose first n//2 vertices form one side and the rest the other.
    Extra edges only shorten distances, so diameter and bipartiteness are preserved.
    """
    m = n // 2
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    rng = random.Random(seed)
    new_edges = list(edges)
    for _ in range(3):
        pts = [p for p in range(m) if deg[p] < d]
        rng.shuffle(pts)
        for p in pts:
            if deg[p] >= d:
                continue
            cands = [l for l in range(m, n) if deg[l] < d and l not in adj[p]]
            if not cands:
                continue
            l = rng.choice(cands)
            adj[p].add(l)
            adj[l].add(p)
            deg[p] += 1
            deg[l] += 1
            new_edges.append((p, l))
    return n, new_edges


def _pg_augmented(d, seed):
    """Incidence graph of PG(2,q) with q the largest prime power <= d-1, plus spare-degree edges."""
    q = _largest_prime_power(d - 1)
    if q is None:
        return None
    n, edges = lib.projective_plane_incidence(q)
    return _spare_augment(n, edges, d, seed)


def _gq_incidence(q):
    """Point-line incidence graph of the generalized quadrangle W(q), or None.

    Points are all points of PG(3,q); lines are totally isotropic lines of the symplectic form
    x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree q+1, bipartite, diameter 4, girth 8.
    Points are 0..P-1 and lines P..2P-1.
    """
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def normalize(v):
        c = next(c for c in v if c)
        ci = F.inv(c)
        return tuple(F.mul(ci, x) for x in v)

    def isotropic(x, y):
        a = F.add(F.mul(x[0], y[1]), F.mul(x[2], y[3]))
        b = F.add(F.mul(x[1], y[0]), F.mul(x[3], y[2]))
        return a == b

    seen_pairs = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in seen_pairs:
                continue
            y = pts[j]
            if not isotropic(x, y):
                continue
            members = {i, j}
            for b in range(q):
                w = tuple(F.add(x[t], F.mul(b, y[t])) for t in range(4))
                members.add(index[normalize(w)])
            mem = sorted(members)
            for a in range(len(mem)):
                for c in range(a + 1, len(mem)):
                    seen_pairs.add((mem[a], mem[c]))
            lines.append(mem)
    if len(lines) != P:
        return None
    edges = [(p, P + l) for l, mem in enumerate(lines) for p in mem]
    return 2 * P, edges


def _gq_augmented(d, seed):
    """W(q) incidence graph with q the largest prime power <= d-1, plus spare-degree edges."""
    q = _largest_prime_power(d - 1)
    if q is None:
        return None
    base = _gq_incidence(q)
    if base is None:
        return None
    return _spare_augment(base[0], base[1], d, seed)


# ----------------------------------------------------------------------------
# NEW: incremental pair growth with exact distance bookkeeping.
#
# Start from an exact-degree-deficient bipartite base of diameter D (projective
# plane or generalized quadrangle incidence graph). Each step adds two fresh
# vertices a (side 0) and b (side 1). We then greedily add A-B edges incident to
# a or b, choosing the edge that fixes the most currently-bad pairs. Distances
# are maintained exactly: adding an edge (u, v) updates
#     dist(x, y) <- min(dist(x, y), dist(x, u) + 1 + dist(v, y), dist(x, v) + 1 + dist(u, y)).
# A pair is accepted only if every pair is within distance D again; otherwise
# the attempt is rolled back.
# ----------------------------------------------------------------------------

def _bfs_dist(adj, n0, cap, INF):
    """All-pairs BFS distances on the base graph, padded to a cap x cap matrix (INF = unreachable)."""
    Dist = np.full((cap, cap), INF, dtype=np.int32)
    for s in range(n0):
        row = [INF] * n0
        row[s] = 0
        frontier = [s]
        level = 0
        while frontier:
            level += 1
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if row[v] == INF:
                        row[v] = level
                        nxt.append(v)
            frontier = nxt
        Dist[s, :n0] = row
    idx = np.arange(cap)
    Dist[idx, idx] = 0
    return Dist


def _attempt(n, Dist, Adj, deg, side, d, D, rng, deadline):
    """Try to add vertices a=n (side 0) and b=n+1 (side 1) so all pairs are within D.

    On success returns the list of added edges (state updated in place).
    On failure rolls back everything and returns None.
    """
    a, b = n, n + 1
    act = n + 2
    snap = Dist[:act, :act].copy()
    added = []
    ok = False
    while True:
        view = Dist[:act, :act]
        bad = view > D
        if not bad.any():
            ok = True
            break
        if time.monotonic() > deadline:
            break
        cands = []
        if deg[a] < d and deg[b] < d and not Adj[a, b]:
            cands.append((a, b))
        if deg[a] < d:
            for y in range(n):
                if side[y] == 1 and deg[y] < d and not Adj[a, y]:
                    cands.append((a, y))
        if deg[b] < d:
            for x in range(n):
                if side[x] == 0 and deg[x] < d and not Adj[x, b]:
                    cands.append((x, b))
        best_g, best = 0, []
        for u, v in cands:
            Du = Dist[:act, u]
            Dv = Dist[:act, v]
            newly = bad & ((Du[:, None] + 1 + Dv[None, :] <= D) |
                           (Dv[:, None] + 1 + Du[None, :] <= D))
            g = int(np.count_nonzero(newly))
            if g > best_g:
                best_g, best = g, [(u, v)]
            elif g == best_g and g > 0:
                best.append((u, v))
        if best_g == 0:
            break
        u, v = best[rng.randrange(len(best))]
        Du = Dist[:act, u].copy()
        Dv = Dist[:act, v].copy()
        upd = np.minimum(Du[:, None] + 1 + Dv[None, :], Dv[:, None] + 1 + Du[None, :])
        np.minimum(view, upd, out=view)
        Adj[u, v] = True
        Adj[v, u] = True
        deg[u] += 1
        deg[v] += 1
        added.append((u, v))
    if ok:
        return added
    for u, v in added:
        Adj[u, v] = False
        Adj[v, u] = False
        deg[u] -= 1
        deg[v] -= 1
    Dist[:act, :act] = snap
    return None


def _grow(base_n, base_edges, d, D, seed, deadline, max_pairs=GROW_PAIRS):
    """Grow a bipartite base of diameter D by adding (side0, side1) vertex pairs.

    Side 0 = indices < base_n // 2 (plus new even offsets), side 1 = the rest.
    Returns (n, edges) with n > base_n, or None if no pair could be added.
    """
    rng = random.Random(seed)
    m0 = base_n // 2
    cap = base_n + 2 * max_pairs
    INF = 1000
    adj = [[] for _ in range(base_n)]
    for u, v in base_edges:
        adj[u].append(v)
        adj[v].append(u)
    Dist = _bfs_dist(adj, base_n, cap, INF)
    Adj = np.zeros((cap, cap), dtype=bool)
    for u, v in base_edges:
        Adj[u, v] = True
        Adj[v, u] = True
    side = [0 if i < m0 else (1 if i < base_n else (i - base_n) % 2) for i in range(cap)]
    deg = [0] * cap
    for u, v in base_edges:
        deg[u] += 1
        deg[v] += 1
    edges_out = list(base_edges)
    n = base_n
    for _ in range(max_pairs):
        if time.monotonic() > deadline:
            break
        got = None
        for _try in range(3):
            got = _attempt(n, Dist, Adj, deg, side, d, D, rng, deadline)
            if got is not None:
                break
        if got is None:
            break
        edges_out.extend(got)
        n += 2
    if n == base_n:
        return None
    return n, edges_out


def _grown_candidate(d, D, seed, deadline):
    """Grow the raw PG(2,q) (D=3) or W(q) (D=4) incidence graph into spare degree, q = largest prime power <= d-1."""
    q = _largest_prime_power(d - 1)
    if q is None or d - (q + 1) <= 0:
        return None
    if D == 3:
        base = lib.projective_plane_incidence(q)
    elif D == 4:
        base = _gq_incidence(q)
    else:
        return None
    if base is None:
        return None
    n0, e0 = base
    if not lib.is_valid(n0, e0, q + 1, D):
        return None
    return _grow(n0, e0, d, D, seed, deadline)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.6 * time_limit - 1.0)
    grow_deadline = start + max(0.5, 0.85 * time_limit - 1.0)

    # Trivial fallbacks, always valid where stated.
    if D >= 2 and d >= 1:
        fallback = lib.haar_graph(d, range(d))      # K_{d,d}: diameter 2
    elif D >= 1 and d >= 1:
        fallback = (2, [(0, 1)])                     # K_2
    else:
        fallback = (1, [])

    # D = 3: projective-plane based construction (exact when d-1 is a prime power,
    # otherwise augmented with spare degree from PG(2, q), q the largest prime power <= d-1).
    pg = None
    if D == 3 and d >= 3:
        cand = _pg_augmented(d, seed)
        if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
            pg = cand
            if lib.is_prime_power(d - 1):
                return pg

    # D = 4: generalized quadrangle W(q) incidence graph (degree q+1, diameter 4),
    # exact when d-1 is a prime power, otherwise augmented with spare degree.
    gq = None
    if D == 4 and d >= 3:
        cand = _gq_augmented(d, seed)
        if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
            gq = cand
            if lib.is_prime_power(d - 1):
                return gq

    if D < 2 or d < 1:
        return fallback

    rng = random.Random(seed)
    cap = min(N_CAP, lib._moore_bound(d, D))
    best = None  # (n, s, m, P, V)
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(S_LIST) - idx)
        res = _search(s, d, D, rng, slice_end, cap)
        if res is not None:
            m, P, V = res
            n = 2 * s * m
            if best is None or n > best[0]:
                best = (n, s, m, P, V)

    lift = None
    if best is not None:
        n, e = _graph(best[1], best[2], best[3], best[4], d)
        if lib.is_valid(n, e, d, D):
            lift = (n, e)

    # NEW: pair growth into spare degree of the raw incidence graph (D = 3 or 4).
    grown = None
    if D in (3, 4) and d >= 3 and time.monotonic() < grow_deadline - 0.5:
        g = _grown_candidate(d, D, seed, grow_deadline)
        if g is not None and lib.is_valid(g[0], g[1], d, D):
            grown = g

    # Return the largest valid candidate.
    options = [c for c in (pg, gq, lift, grown, fallback) if c is not None]
    return max(options, key=lambda c: c[0])
