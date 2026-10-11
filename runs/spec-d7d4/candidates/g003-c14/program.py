import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: projective plane (D = 3) and generalized quadrangle W(q) (D = 4).
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


def _extend_cover(n, edges, d, D, deadline, rng, always_random=False):
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
                chosen = _greedy_cover(cands, ball, full, d, rng, always_random or attempt > 0)
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


def _grow(n, edges, d, D, deadline, rng, always_random=False):
    """Extend by cover vertices, then saturate edges with the leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, always_random)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Direct repair search: add a few vertices to a valid graph and locally search
# (degree-preserving 2-switches, endpoint moves, and edge additions) to restore
# diameter D while keeping bipartiteness and max degree d.
# ----------------------------------------------------------------------------

def _repair(n, edges, d, D, extra, deadline, rng):
    """Try to find a valid graph on n + extra vertices; return (N, edges) or None."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = _bipartition(n, adj)
    N = n + extra
    col = col + [k % 2 for k in range(extra)]
    E = [(u, v) if col[u] == 0 else (v, u) for u, v in edges]
    keys = set(E)
    cost = lib.bad_pairs(N, E, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = 0.6 * (0.01 ** ((now - t0) / span))

        deg = [0] * N
        for a, b in E:
            deg[a] += 1
            deg[b] += 1
        A = [v for v in range(N) if col[v] == 0]
        B = [v for v in range(N) if col[v] == 1]
        defA = [v for v in A if deg[v] < d]
        defB = [v for v in B if deg[v] < d]

        r = rng.random()
        edits = None
        if r < 0.35 and len(E) >= 2:
            i = rng.randrange(len(E))
            j = rng.randrange(len(E))
            if i != j:
                a1, b1 = E[i]
                a2, b2 = E[j]
                if (a1 != a2 and b1 != b2
                        and (a1, b2) not in keys and (a2, b1) not in keys):
                    edits = [(i, (a1, b2)), (j, (a2, b1))]
        elif r < 0.7:
            if not E:
                continue
            i = rng.randrange(len(E))
            a, b = E[i]
            if defA and (rng.random() < 0.5 or not defB):
                x = rng.choice(defA)
                if x != a and (x, b) not in keys:
                    edits = [(i, (x, b))]
            elif defB:
                y = rng.choice(defB)
                if y != b and (a, y) not in keys:
                    edits = [(i, (a, y))]
        else:
            if defA and defB:
                a = rng.choice(defA)
                b = rng.choice(defB)
                if (a, b) not in keys:
                    edits = [(None, (a, b))]
        if edits is None:
            continue

        # Apply the edit, remembering how to undo it.
        olds = []
        for i, e in edits:
            olds.append(None if i is None else E[i])
        for i, e in edits:
            if i is None:
                E.append(e)
                keys.add(e)
            else:
                keys.discard(E[i])
                E[i] = e
                keys.add(e)

        nc = lib.bad_pairs(N, E, D)
        if nc <= cost or rng.random() < math.exp(-(nc - cost) / T):
            cost = nc
        else:
            for k in range(len(edits) - 1, -1, -1):
                i, e = edits[k]
                if i is None:
                    E.pop()
                    keys.discard(e)
                else:
                    keys.discard(e)
                    E[i] = olds[k]
                    keys.add(olds[k])

    return N, E


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

    # Structured bases.
    bases = []
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            bases.append(pg)
    elif D >= 4:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            if time.monotonic() >= start + 0.2 * time_limit:
                break
            bases.append(_gq_w(q))
    for b in bases:
        consider(b[0], b[1])

    # Growth from each base, with a bounded budget.
    if D >= 3:
        grow_deadline = start + 0.35 * time_limit
        for b in bases:
            if time.monotonic() >= grow_deadline:
                break
            n2, e2 = _grow(b[0], b[1], d, D, grow_deadline, rng)
            consider(n2, e2)

    # Repair search from the best valid graph found so far, alternating +2 and +1.
    fails = 0
    while time.monotonic() < deadline:
        now = time.monotonic()
        rem = deadline - now
        slice_end = now + max(rem * 0.5, min(rem, 3.0))
        extra = 2 if fails % 2 == 0 else 1
        res = _repair(best_n, best[1], d, D, extra, slice_end, rng)
        if res is not None:
            consider(res[0], res[1])
            fails = 0
        else:
            fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
