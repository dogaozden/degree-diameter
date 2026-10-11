import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold alternative for D = 3: annealed growth on a valid projective-plane base.
#
# Base: incidence graph of PG(2, q) plus, when spare degree allows, a conic arc
# extension (the known record family). Growth: keep a valid graph of order n,
# add one vertex joined to spare-degree vertices on the other side, then anneal
# with degree-preserving double-edge swaps and edge additions, minimizing the
# number of vertex pairs at distance > 3. Whenever the cost reaches 0 the graph
# is verified with lib.is_valid and stored, and the search grows again.
# Every stored graph is valid, so the fallback is always safe.
# ----------------------------------------------------------------------------


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable counts)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set; an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_ext(q, m, E, s, d, D):
    """Extend PG(2,q) incidence by an A-vertex per conic point and a B-vertex per conic line."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in E:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    S = _conic_set(q, index, F)
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    if max(cl, default=0) > s or max(cp, default=0) > s:
        return None
    k = len(S)
    n = 2 * m + 2 * k
    side = [0] * m + [1] * m + [0] * k + [1] * k
    ext = list(E)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            ext.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            ext.append((Q, b))
    if not lib.is_valid(n, ext, d, D):
        return None
    return n, ext, side


def _pg_base(d, D):
    """Best valid projective-plane based graph among the largest few prime powers q."""
    cands = []
    used = 0
    for q in range(min(d - 1, 23), 1, -1):
        if not lib.is_prime_power(q):
            continue
        if used >= 3:
            break
        used += 1
        n2, E = lib.projective_plane_incidence(q)
        m = n2 // 2
        side = [0] * m + [1] * m
        cands.append((n2, list(E), side))
        s = d - q - 1
        if D >= 3 and s >= 2:
            ext = _arc_ext(q, m, E, s, d, D)
            if ext is not None:
                cands.append(ext)
    valid = [c for c in cands if lib.is_valid(c[0], c[1], d, D)]
    return max(valid, key=lambda c: c[0], default=None)


def _state(n, E, side):
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    L = [[v for v in range(n) if side[v] == 0], [v for v in range(n) if side[v] == 1]]
    return adj, L


def _grow(n0, E0, side0, d, D, deadline, rng):
    """Anneal-and-grow search for D = 3. Returns the largest valid (n, edges) found."""
    best = (n0, list(E0), list(side0))
    n = n0
    side = list(side0)
    adj, L = _state(n, E0, side)
    cur = _bad(n, adj, D)
    best_cur = cur
    T = 0.6
    stale = 0

    while time.monotonic() < deadline:
        if cur == 0:
            E = [(u, v) for u in range(n) for v in adj[u] if u < v]
            if n > best[0] and lib.is_valid(n, E, d, D):
                best = (n, E, list(side))
            # Grow by one vertex attached to spare-degree vertices on the other side.
            s = rng.randrange(2)
            cands = None
            ss = s
            for cand_side in (s, 1 - s):
                cands = [v for v in L[1 - cand_side] if len(adj[v]) < d]
                if cands:
                    ss = cand_side
                    break
            if not cands:
                break
            rng.shuffle(cands)
            nb = cands[:d]
            x = n
            n += 1
            adj.append(set())
            side.append(ss)
            L[ss].append(x)
            for v in nb:
                adj[x].add(v)
                adj[v].add(x)
            cur = _bad(n, adj, D)
            best_cur = cur
            T = 0.6
            stale = 0
            continue

        stale += 1
        if stale > 4000:
            # Restart from the best valid graph.
            n, E_b, side_b = best[0], best[1], best[2]
            n = best[0]
            side = list(side_b)
            adj, L = _state(n, E_b, side)
            cur = _bad(n, adj, D)
            best_cur = cur
            T = 0.6
            stale = 0
            continue

        T = max(0.15, T * 0.9995)
        if rng.random() < 0.25:
            a = rng.choice(L[0])
            b = rng.choice(L[1])
            if len(adj[a]) >= d or len(adj[b]) >= d or b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            cur = _bad(n, adj, D)  # adding an edge never increases the cost
        else:
            a1 = rng.choice(L[0])
            if not adj[a1]:
                continue
            b1 = rng.choice(tuple(adj[a1]))
            a2 = rng.choice(L[0])
            if not adj[a2]:
                continue
            b2 = rng.choice(tuple(adj[a2]))
            if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
                continue
            adj[a1].discard(b1)
            adj[b1].discard(a1)
            adj[a2].discard(b2)
            adj[b2].discard(a2)
            adj[a1].add(b2)
            adj[b2].add(a1)
            adj[a2].add(b1)
            adj[b1].add(a2)
            new = _bad(n, adj, D)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
            else:
                adj[a1].discard(b2)
                adj[b2].discard(a1)
                adj[a2].discard(b1)
                adj[b1].discard(a2)
                adj[a1].add(b1)
                adj[b1].add(a1)
                adj[a2].add(b2)
                adj[b2].add(a2)

        if cur < best_cur:
            best_cur = cur
            stale = 0

    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = (fb_n, list(fb_e))

    if D == 2:
        return best

    base = _pg_base(d, D)
    if base is not None and base[0] > best[0]:
        best = (base[0], list(base[1]))

    if D == 3 and base is not None:
        res = _grow(base[0], base[1], base[2], d, D, deadline, rng)
        if res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = (res[0], list(res[1]))

    if not lib.is_valid(best[0], best[1], d, D):
        best = (fb_n, list(fb_e))
    return best
