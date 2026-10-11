import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1: arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Optionally delete a matching R of
# incidences, which frees capacity. Then add one new vertex per chosen point
# (joined to its q+1 lines) and one per chosen line (joined to its q+1 points),
# subject to per-element capacities. Every candidate is validated.
# ----------------------------------------------------------------------------

_LS_ITERS = 12000


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


def _loads_ok(S, caps, nbr):
    """True if every target t is hit by <= caps[t] elements of S."""
    m = len(caps)
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return all(load[t] <= caps[t] for t in range(m))


def _greedy_side(m, caps, nbr, rng, trials, deadline):
    """Randomized greedy capacitated set."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < caps[t] for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_search(m, caps, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the capacitated set problem."""
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= caps[t]:
                if not cur:
                    ok = False
                    break
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _best_side(m, caps, nbr, rng, deadline, seeds):
    """Best capacitated set from greedy, supplied seeds, then local search."""
    cands = [_greedy_side(m, caps, nbr, rng, 12, deadline)]
    for S in seeds:
        if _loads_ok(S, caps, nbr):
            cands.append(list(S))
    start = max(cands, key=len)
    return _local_search(m, caps, nbr, start, rng, deadline, _LS_ITERS)


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _pick_deletions(edges, m, r, rng):
    """Random matching of up to r PG incidences, as (point, line) pairs."""
    inc = [(u, v - m) for u, v in edges]
    rng.shuffle(inc)
    usedP, usedL, R = set(), set(), []
    for P, L in inc:
        if len(R) >= r:
            break
        if P in usedP or L in usedL:
            continue
        usedP.add(P)
        usedL.add(L)
        R.append((P, L))
    return R


def _arc_graph(m, edges, R, point_lines, line_points, SA, SB):
    """PG incidence minus deleted matching R, plus A-vertices and B-vertices."""
    Rset = set(R)
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = [(u, v) for u, v in edges if (u, v - m) not in Rset]
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * (s + 1) * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        q_deadline = now + (deadline - now) / (len(qs) - idx)
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        conic = _conic_set(q, index, lib.GF(q)) if s >= 0 else []
        rs = [0, max(1, m // 12), max(1, m // 6), max(1, m // 4)]
        trial = 0
        while time.monotonic() < q_deadline:
            r = rs[trial] if trial < len(rs) else rng.choice(rs)
            trial += 1
            R = _pick_deletions(edges, m, r, rng) if r > 0 else []
            delP = [0] * m
            delL = [0] * m
            for P, L in R:
                delP[P] += 1
                delL[L] += 1
            capL = [s + delL[L] for L in range(m)]
            capP = [s + delP[P] for P in range(m)]
            seeds = [conic] if not R else []
            SA = _best_side(m, capL, point_lines, rng, q_deadline, seeds)
            SB = _best_side(m, capP, line_points, rng, q_deadline, seeds)
            if not (_loads_ok(SA, capL, point_lines) and _loads_ok(SB, capP, line_points)):
                continue
            out.append(_arc_graph(m, edges, R, point_lines, line_points, SA, SB))
            if trial > 40:
                break
    out.sort(key=lambda t: -t[0])
    return out[:30]


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Stage 2 (new, bold): greedy vertex insertion with edge-swap repair.
#
# Invariant: the current graph is always bipartite, has max degree <= d and
# diameter <= D. Adding a new vertex x of colour c, joined to a set S of
# opposite-colour vertices with spare degree, keeps old pairs valid (new paths
# can only shorten distances). x is valid iff every old vertex lies within
# distance D-1 of S, i.e. S's radius-(D-1) balls cover all vertices.
#
# Moves:
#   insert : find such an S greedily (max coverage) and add x.
#   swap   : remove a random edge to free a slot, then insert; keep the result
#            only if the full graph still has diameter <= D.
# ----------------------------------------------------------------------------

def _reach(adj, n, r):
    """Per-vertex bitmask of all vertices within distance r."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        reach = new
    return reach


def _all_within(adj, n, D):
    full = (1 << n) - 1
    return all(r == full for r in _reach(adj, n, D))


def _two_color(adj, n):
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


def _cover_pick(B, cand, full, d, rng):
    """Greedy max-coverage choice of up to d candidates whose balls cover full."""
    covered = 0
    S = []
    pool = list(cand)
    for _ in range(d):
        best = None
        bestgain = 0
        for s in pool:
            g = (B[s] & ~covered).bit_count()
            if g > bestgain or (g == bestgain and g > 0 and rng.random() < 0.3):
                best, bestgain = s, g
        if best is None or bestgain == 0:
            break
        S.append(best)
        covered |= B[best]
        pool.remove(best)
        if covered & full == full:
            return S
    return None


def _add_vertex(adj, color, S, c):
    x = len(adj)
    adj.append(set())
    color.append(c)
    for s in S:
        adj[x].add(s)
        adj[s].add(x)


def _pop_vertex(adj, color):
    x = len(adj) - 1
    for s in adj[x]:
        adj[s].discard(x)
    adj.pop()
    color.pop()


def _grow(n0, edges0, d, D, deadline, rng):
    """Repeatedly insert vertices (with swap repair) while time remains."""
    adj = [set() for _ in range(n0)]
    for u, v in edges0:
        adj[u].add(v)
        adj[v].add(u)
    color = _two_color(adj, n0)

    while time.monotonic() < deadline:
        n = len(adj)
        c = rng.randrange(2)
        B = _reach(adj, n, D - 1)
        full = (1 << n) - 1
        cand = [v for v in range(n) if color[v] != c and len(adj[v]) < d]
        rng.shuffle(cand)
        S = _cover_pick(B, cand, full, d, rng)
        if S is not None:
            _add_vertex(adj, color, S, c)
            continue

        # Swap move: free a slot by removing an edge at a random colour-c vertex.
        pool = [v for v in range(n) if color[v] == c and adj[v]]
        if not pool:
            continue
        a = rng.choice(pool)
        b = rng.choice(sorted(adj[a]))
        adj[a].discard(b)
        adj[b].discard(a)
        B = _reach(adj, n, D - 1)
        cand = [v for v in range(n) if color[v] != c and len(adj[v]) < d]
        rng.shuffle(cand)
        S = _cover_pick(B, cand, full, d, rng)
        ok = False
        if S is not None:
            _add_vertex(adj, color, S, c)
            if _all_within(adj, n + 1, D):
                ok = True
            else:
                _pop_vertex(adj, color)
        if not ok:
            adj[a].add(b)
            adj[b].add(a)

    n = len(adj)
    edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, edges


# ----------------------------------------------------------------------------
# build()
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Stage 1: arc-extended projective plane graphs (D >= 3).
    if D >= 3:
        cands = _arc_extensions(d, start + 0.40 * time_limit,
                                random.Random(seed * 7919 + d))
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    # Stage 1b: generalized quadrangle for D >= 4.
    if D >= 4 and time.monotonic() < start + 0.45 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Stage 2: greedy insertion with swap repair, started from the best valid graph.
    deadline = start + 0.85 * time_limit
    if time.monotonic() < deadline:
        try:
            n_g, e_g = _grow(best[0], best[1], d, D, deadline, rng)
            consider(n_g, e_g)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
