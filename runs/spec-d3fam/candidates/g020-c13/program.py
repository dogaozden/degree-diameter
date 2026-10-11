import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane and generalized-quadrangle bases.
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Growth helpers (diameter-preserving cover extension, then edge saturation).
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


def _extend_cover(n, edges, d, D, deadline, rng):
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
# NEW FAMILY for D = 3: vertex deletion from a larger projective plane PG(2, q),
# followed by randomized repair (saturate spare degree, delete the vertex that
# leaves the most unreachable pairs). Degrees never increase under deletion, so
# only the diameter and bipartiteness need checking.
# ----------------------------------------------------------------------------

def _pg_adj(q):
    n, edges = lib.projective_plane_incidence(q)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return n, adj


def _delete(v, adj, alive):
    alive[v] = False
    for u in adj[v]:
        adj[u].discard(v)
    adj[v] = set()


def _thin(adj, alive, d, rng, deadline):
    """Delete vertices until every surviving vertex has degree <= d. Greedy: take the
    neighbour that relieves the most over-degree vertices. Returns False on timeout."""
    N = len(adj)
    while time.monotonic() < deadline:
        over = [v for v in range(N) if alive[v] and len(adj[v]) > d]
        if not over:
            return True
        cands = set()
        for v in over:
            cands.update(adj[v])
        cands = list(cands)
        rng.shuffle(cands)
        best, bs = None, -1
        for x in cands:
            s = sum(1 for u in adj[x] if len(adj[u]) > d)
            if s > bs:
                best, bs = x, s
        _delete(best, adj, alive)
    return False


def _saturate(adj, alive, d, m, rng):
    """Add point-line edges between deficient vertices (vertices < m are points)."""
    N = len(adj)
    L = [v for v in range(N) if alive[v] and v < m and len(adj[v]) < d]
    R = [v for v in range(N) if alive[v] and v >= m and len(adj[v]) < d]
    rng.shuffle(L)
    for a in L:
        if len(adj[a]) >= d:
            continue
        opts = [b for b in R if len(adj[b]) < d and b not in adj[a]]
        rng.shuffle(opts)
        for b in opts:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) < d:
                adj[a].add(b)
                adj[b].add(a)


def _balls_alive(adj, alive, D):
    N = len(adj)
    reach = [(1 << v) if alive[v] else 0 for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            if alive[v]:
                x = reach[v]
                for u in adj[v]:
                    x |= reach[u]
                new[v] = x
        reach = new
    return reach


def _repair(adj, alive, d, D, m, deadline, rng):
    """Saturate, then delete the vertex with the most unreachable pairs, until valid."""
    N = len(adj)
    while time.monotonic() < deadline:
        _saturate(adj, alive, d, m, rng)
        A = sum(alive)
        reach = _balls_alive(adj, alive, D)
        miss = [A - reach[v].bit_count() if alive[v] else 0 for v in range(N)]
        mx = max(miss, default=0)
        if mx == 0:
            return True
        pool = [v for v in range(N) if miss[v] == mx]
        _delete(rng.choice(pool), adj, alive)
    return False


def _export(adj, alive):
    ids = [v for v in range(len(adj)) if alive[v]]
    idx = {v: i for i, v in enumerate(ids)}
    E = [(idx[v], idx[u]) for v in ids for u in adj[v] if v < u]
    return len(ids), E


def _deletion_family(d, D, deadline, rng, consider, best_n_fn):
    qs = [q for q in range(max(2, d - 3), d + 4) if lib.is_prime_power(q)]
    qs.sort(key=lambda q: abs(q + 1 - d))
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now >= deadline:
            break
        sub_deadline = now + (deadline - now) / (len(qs) - idx)
        n0, adj0 = _pg_adj(q)
        m = n0 // 2
        while time.monotonic() < sub_deadline:
            adj = [set(s) for s in adj0]
            alive = [True] * n0
            if not _thin(adj, alive, d, rng, sub_deadline):
                break
            if not _repair(adj, alive, d, D, m, sub_deadline, rng):
                continue
            n, e = _export(adj, alive)
            if n <= best_n_fn():
                continue
            consider(n, e)
            gn, ge = _grow(n, e, d, D, sub_deadline, rng)
            consider(gn, ge)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Araujo-Pardo & Lopez record family for d = q + 2, q a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                consider(n_a, e_a)
            except Exception:
                pass
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        if D == 3:
            try:
                _deletion_family(d, D, start + 0.75 * time_limit, rng,
                                 consider, lambda: best_n)
            except Exception:
                pass

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, deadline, rng)
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
