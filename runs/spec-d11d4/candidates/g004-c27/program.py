import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: projective plane and generalized quadrangle incidence graphs.
# ----------------------------------------------------------------------------

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


def _best_pg(d):
    """PG(2, q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 9 for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared utilities.
# ----------------------------------------------------------------------------

def _adj_of(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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


def _cover_ls(cands, ball, full, d, rng, steps, deadline):
    """Swap-based local search for a cover of `full` by d candidate balls."""
    if not cands:
        return None
    k = min(d, len(cands))
    S = rng.sample(cands, k)
    in_s = set(S)

    def union(sel):
        u = 0
        for s in sel:
            u |= ball[s]
        return u

    cost = (full & ~union(S)).bit_count()
    for step in range(steps):
        if cost == 0:
            break
        if (step & 255) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        rest = S[:i] + S[i + 1:]
        miss = full & ~union(rest)
        best_t, best_g = None, -1
        for t in rng.sample(cands, min(30, len(cands))):
            if t in in_s:
                continue
            g = (ball[t] & miss).bit_count()
            if g > best_g:
                best_t, best_g = t, g
        if best_t is None:
            continue
        newcost = (miss & ~ball[best_t]).bit_count()
        if newcost <= cost or rng.random() < 0.02:
            in_s.discard(S[i])
            S[i] = best_t
            in_s.add(best_t)
            cost = newcost
    return S if cost == 0 else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover all vertices within D-1 (monotone, keeps validity)."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = _adj_of(n, edges)
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
            for attempt in range(25):
                if time.monotonic() >= deadline:
                    break
                if attempt < 5:
                    chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                else:
                    chosen = _cover_ls(cands, ball, full, d, rng, 2000, deadline)
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
    """Greedily join deficient opposite-side vertices (adding edges never breaks validity)."""
    edges = list(edges)
    adj = _adj_of(n, edges)
    existing = set()
    for u, v in edges:
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
    """Extend by cover vertices, then saturate edges with leftover spare degree."""
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


def _greedy_partial(cands, ball, full, d, rng):
    """Pick up to d candidates greedily by coverage; return (chosen, number uncovered)."""
    pool = list(cands)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while pool and len(chosen) < d:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        mx = max(gains)
        if mx == 0:
            break
        idx = [i for i, g in enumerate(gains) if g == mx]
        i = rng.choice(idx)
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen, (full & ~covered).bit_count()


def _partial_insert(n, edges, d, D, rng, deadline, max_sweeps):
    """Insert one vertex with partial cover, then 2-switch repair. Returns (n, edges) or None."""
    adj = _adj_of(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    ball = _balls_radius(n, adj, D - 1)
    full = (1 << n) - 1

    best = None
    for c in (0, 1):
        cands = [s for s in range(n) if color[s] == c and deg[s] < d]
        if not cands:
            continue
        chosen, miss = _greedy_partial(cands, ball, full, d, rng)
        if chosen and (best is None or miss < best[1]):
            best = (chosen, miss, c)
    if best is None:
        return None
    chosen, _, c = best

    v = n
    N = n + 1
    E = []
    for u, w in edges:
        E.append((u, w) if color[u] == 0 else (w, u))
    for s in chosen:
        E.append((s, v) if c == 0 else (v, s))
    Eset = set(E)

    bad = lib.bad_pairs(N, E, D)
    sweeps = 0
    while bad > 0 and sweeps < max_sweeps and time.monotonic() < deadline and len(E) >= 2:
        sweeps += 1
        i, j = rng.sample(range(len(E)), 2)
        x1, y1 = E[i]
        x2, y2 = E[j]
        if x1 == x2 or y1 == y2:
            continue
        a = (x1, y2)
        b = (x2, y1)
        if a in Eset or b in Eset:
            continue
        E[i] = a
        E[j] = b
        Eset.discard((x1, y1))
        Eset.discard((x2, y2))
        Eset.add(a)
        Eset.add(b)
        nb = lib.bad_pairs(N, E, D)
        if nb <= bad:
            bad = nb
        else:
            E[i] = (x1, y1)
            E[j] = (x2, y2)
            Eset.discard(a)
            Eset.discard(b)
            Eset.add((x1, y1))
            Eset.add((x2, y2))
    if bad > 0:
        return None
    return N, E


def _remove_vertices(n, edges, victims):
    """Delete the given vertices and relabel the rest to 0..n'-1 preserving order."""
    vs = set(victims)
    keep = [v for v in range(n) if v not in vs]
    idx = {v: i for i, v in enumerate(keep)}
    out = [(idx[u], idx[v]) for u, v in edges if u in idx and v in idx]
    return len(keep), out


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget
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

    if D == 2:
        return best

    try:
        # Choose the base: the largest valid one among the available constructions.
        base = None
        bases = []
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                bases.append(pg)
        if D >= 4:
            gq = _best_gq(d)
            if gq is not None:
                bases.append(gq)
        bases.sort(key=lambda g: -g[0])
        for n0, e0 in bases:
            if lib.is_valid(n0, e0, d, D):
                consider(n0, e0)
                base = (n0, e0)
                break

        if base is not None:
            base_n, base_e = base
            cur = _grow(base_n, base_e, d, D, start + 0.3 * budget, rng)
            consider(cur[0], cur[1])
            best_state = cur

            fails = 0
            while time.monotonic() < deadline:
                cur_n, cur_e = cur
                # Fully saturated base with no added vertices: nothing more to do.
                if cur_n == base_n and 2 * len(cur_e) >= d * cur_n:
                    break

                if fails >= 6:
                    # Perturb the best graph: remove a few added vertices, then resaturate.
                    bn, be = best_state
                    added_count = bn - base_n
                    if added_count > 0:
                        k = min(added_count, rng.choice([1, 1, 2, 2, 3, 5]))
                        victims = rng.sample(range(base_n, bn), k)
                        pn, pe = _remove_vertices(bn, be, victims)
                        pe = _saturate_edges(pn, pe, d, rng)
                        if lib.is_valid(pn, pe, d, D):
                            cur = (pn, pe)
                        else:
                            cur = best_state
                    else:
                        cur = best_state
                    fails = 0
                    continue

                res = _partial_insert(cur_n, cur_e, d, D, rng, deadline, 40)
                if res is None:
                    fails += 1
                    continue
                n2, e2 = res
                e2 = _saturate_edges(n2, e2, d, rng)
                cur = (n2, e2)
                fails = 0
                if n2 > best_state[0]:
                    best_state = cur
                consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
