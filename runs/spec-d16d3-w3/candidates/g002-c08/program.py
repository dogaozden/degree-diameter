"""Bipartite (d, D) builder built around decoupled dual arcs over PG(2, q).

New construction (not in the parent): for PG(2, q) with spare degree s = d - q - 1,
pick two independent point sets. S gets a new A-vertex per point (adjacent to the
q+1 lines through it), and T gets a new B-vertex per line (adjacent to the q+1
points on it). Each line may meet at most s points of S, and each point may lie
on at most s lines of T. The two sets are searched independently, since PG(2, q)
is self-dual and the same load routine serves both.

Diameter 3 is preserved for arbitrary S and T. For example, x_P to y_L can go
x_P - PQ - Q - y_L for any point Q on L. The coupled arc graph of the parent is
the special case T = S, so this family is never worse.

Remaining spare degree is then used by cover-based vertex growth, which only adds
vertices and edges, so diameter stays valid. Every candidate is checked with
lib.is_valid before it is kept, and K_{d,d} is the fallback.
"""
import random
import time

import lib


def _pg_inc(q):
    """Return (m, inc, edges). Points and lines share the index set 0..m-1 (same vectors).

    inc[i] lists j with point i on line j. The relation is symmetric, so inc[j] also
    gives the points on line j. edges is the incidence graph (points 0..m-1, lines m..2m-1).
    """
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    inc = [[] for _ in range(m)]
    for u, v in edges:
        inc[u].append(v - m)
    return m, inc, edges


def _arc_search(m, s, inc, rng, deadline):
    """Local search for X in 0..m-1 with |X & inc[y]| <= s for every y (dual-arc condition).

    Adding a free element is always taken. A single blocker is swapped out (plateau move).
    Two blockers are swapped only occasionally, to perturb. Returns the largest X seen.
    """
    inX = [False] * m
    X = []
    cl = [0] * m

    def add(x):
        inX[x] = True
        X.append(x)
        for y in inc[x]:
            cl[y] += 1

    def rem(x):
        inX[x] = False
        X.remove(x)
        for y in inc[x]:
            cl[y] -= 1

    def blockers(x):
        sat = {y for y in inc[x] if cl[y] >= s}
        if not sat:
            return []
        return [r for r in X if any(y in sat for y in inc[r])]

    best = []
    it = 0
    while True:
        it += 1
        if (it & 31) == 0 and time.monotonic() >= deadline:
            break
        x = rng.randrange(m)
        if inX[x]:
            continue
        B = blockers(x)
        if not B:
            add(x)
        elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.05):
            for r in B:
                rem(r)
            add(x)
        else:
            continue
        if len(X) > len(best):
            best = list(X)
    return best


def _compose(m, inc, S, T):
    """PG(2,q) incidence plus an A-vertex per point of S and a B-vertex per line of T."""
    n = 2 * m + len(S) + len(T)
    E = []
    for i in range(m):
        for j in inc[i]:
            E.append((i, m + j))
    base_a = 2 * m
    for t, P in enumerate(S):
        for j in inc[P]:
            E.append((base_a + t, m + j))
    base_b = base_a + len(S)
    for t, L in enumerate(T):
        for Q in inc[L]:
            E.append((Q, base_b + t))
    return n, E


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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains)
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
    """Add a vertex whose neighbourhood covers all vertices within D-1 of the graph.

    Adding a vertex never increases a distance, so growth preserves diameter.
    """
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
            for attempt in range(40):
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


def _saturate(n, edges, d, rng):
    """Join deficient opposite-colour vertices in random order (edges only, no new vertices)."""
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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
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
        cur_e = _saturate(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]
    if not qs:
        return best

    # Base: plain projective-plane incidence graph (diameter 3 <= D).
    composites = []
    qmax = max(qs)
    m0, _, pg_edges = _pg_inc(qmax)
    composites.append((2 * m0, pg_edges))
    consider(2 * m0, pg_edges)

    # New family: decoupled dual arcs S (points) and T (lines), each with loads <= s.
    arc_qs = [q for q in qs if d - q - 1 >= 1]
    arc_deadline = start + 0.6 * (deadline - start)
    for idx, q in enumerate(arc_qs):
        now = time.monotonic()
        if now >= arc_deadline:
            break
        share = (arc_deadline - now) / (len(arc_qs) - idx)
        s = d - q - 1
        m, inc, _ = _pg_inc(q)
        slices = 4
        slice_t = share / (2 * slices)
        bestS, bestT = [], []
        for _ in range(slices):
            t_s = _arc_search(m, s, inc, rng, time.monotonic() + slice_t)
            if len(t_s) > len(bestS):
                bestS = t_s
            t_t = _arc_search(m, s, inc, rng, time.monotonic() + slice_t)
            if len(t_t) > len(bestT):
                bestT = t_t
        n_c, e_c = _compose(m, inc, bestS, bestT)
        composites.append((n_c, e_c))
        consider(n_c, e_c)

    # Cover-based growth on the largest candidates, using the spare degree.
    composites.sort(key=lambda c: -c[0])
    top = composites[:2]
    for idx, (n_c, e_c) in enumerate(top):
        now = time.monotonic()
        if now >= deadline:
            break
        sub = now + (deadline - now) / (len(top) - idx)
        n2, e2 = _grow(n_c, e_c, d, D, sub, rng)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
