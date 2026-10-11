import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy (bold rewrite of the growth engine):
#   * Bases: incidence graphs of generalized quadrangles W(q) for D = 4 and
#     projective planes for D = 3, with K_{d,d} as the always-valid fallback.
#   * Growth: repeatedly add a vertex whose neighbourhood covers every existing
#     vertex within distance D-1 (randomized greedy set cover, so runs differ).
#   * Plateau search: a population of valid graphs, each step either regrows a
#     state or first deletes 1-3 random edges (kept only if diameter still holds),
#     then regrows and re-saturates the spare degree. Every accepted graph is
#     checked with lib.is_valid, and the best valid graph is returned.
# ----------------------------------------------------------------------------


def _gq_w(q):
    """Incidence graph of the points and lines of W(q), a generalized quadrangle; diameter 4."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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


def _ball_masks(n, adj, r):
    """Bitmask per vertex of all vertices at distance <= r."""
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


def _cover(cands, ball, full, d, rng):
    """Randomized greedy cover of `full` by at most d candidates; None on failure."""
    pool = list(cands)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full:
        if len(chosen) >= d or not pool:
            return None
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains)
        if best_g <= 0:
            return None
        if rng.random() < 0.6:
            thr = best_g
        else:
            thr = max(1, best_g - rng.randint(1, 3))
        opts = [i for i, g in enumerate(gains) if g >= thr]
        i = rng.choice(opts)
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen


def _grow_once(n, edges, d, D, rng):
    """Add one vertex whose neighbours cover all vertices within distance D-1. None if impossible."""
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    ball = _ball_masks(n, adj, D - 1)
    full = (1 << n) - 1
    sides = [0, 1]
    rng.shuffle(sides)
    for c in sides:
        cands = [s for s in range(n) if color[s] == c and deg[s] < d]
        if not cands:
            continue
        for _ in range(4):
            chosen = _cover(cands, ball, full, d, rng)
            if chosen:
                v = n
                new_edges = list(edges) + [(s, v) for s in chosen]
                return n + 1, new_edges
    return None


def _saturate(n, edges, d, rng):
    """Join deficient opposite-side vertices in random order (never breaks distances or bipartiteness)."""
    edges = list(edges)
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    existing = {(min(u, v), max(u, v)) for u, v in edges}
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


def _pipeline(n, edges, d, D, rng, deadline):
    """Repeated randomized growth with occasional saturation, then final saturation."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        r = _grow_once(cur_n, cur_e, d, D, rng)
        if r is None:
            break
        cur_n, cur_e = r
        if rng.random() < 0.5:
            cur_e = _saturate(cur_n, cur_e, d, rng)
    return cur_n, _saturate(cur_n, cur_e, d, rng)


def _perturb(n, edges, D, rng, k):
    """Delete k random edges; keep the result only if the diameter bound still holds."""
    edges = list(edges)
    for _ in range(k):
        if not edges:
            return None
        idx = rng.randrange(len(edges))
        edges[idx] = edges[-1]
        edges.pop()
    if lib.bad_pairs(n, edges, D) != 0:
        return None
    return edges


def _bases(d, D):
    """Structured valid starting graphs for this (d, D)."""
    out = []
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                out.append(lib.projective_plane_incidence(q))
                break
    elif D >= 4:
        qs = [q for q in range(min(d - 1, 7), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            out.append(_gq_w(q))
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    rng = random.Random(seed * 1000003 + d * 101 + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    fallback = lib.haar_graph(d, range(d))
    if not lib.is_valid(fallback[0], fallback[1], d, D):
        return 1, []
    best_n, best_e = fallback

    states = []
    for n0, e0 in _bases(d, D):
        if time.monotonic() >= deadline:
            break
        if lib.is_valid(n0, e0, d, D):
            states.append((n0, e0))
            if n0 > best_n:
                best_n, best_e = n0, e0

    if not states:
        return best_n, best_e

    # Plateau search over the population of states.
    while time.monotonic() < deadline:
        i = rng.randrange(len(states))
        n0, e0 = states[i]
        src = e0
        if rng.random() < 0.5:
            pert = _perturb(n0, e0, D, rng, rng.randint(1, 3))
            if pert is None:
                continue
            src = pert
        n1, e1 = _pipeline(n0, src, d, D, rng, deadline)
        if n1 < n0:
            continue
        if not lib.is_valid(n1, e1, d, D):
            continue
        states[i] = (n1, e1)
        if n1 > best_n:
            best_n, best_e = n1, e1

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    fallback = lib.haar_graph(d, range(d))
    return fallback
