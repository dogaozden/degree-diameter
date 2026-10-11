import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane and generalized quadrangle bases.
# ----------------------------------------------------------------------------

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
# Load-bounded sets in PG(2, q): the arc-extension bases (valid for diameter 3).
#
# Adding an A-vertex per point of SA (joined to its lines) and a B-vertex per
# line of SB (joined to its points) keeps diameter 3 and bipartiteness, since
# only vertices are added. Requirements: every line meets SA in <= s points,
# every point lies on <= s lines of SB, with s = d - q - 1.
# ----------------------------------------------------------------------------

def _load_ok(S, nb, m, s):
    """True if every target is hit by at most s chosen sources."""
    cnt = [0] * m
    for x in S:
        for t in nb[x]:
            cnt[t] += 1
    return max(cnt, default=0) <= s


def _greedy_load(nb, m, s, rng, trials, deadline):
    """Randomized greedy load-bounded set; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            tg = nb[x]
            if all(load[t] < s for t in tg):
                S.append(x)
                for t in tg:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _improve_load(nb, m, s, S0, rng, deadline, iters):
    """Plateau-walking 1-swap local search for a feasible load-bounded set."""
    load = [0] * m
    inS = [False] * m
    cur = []
    for x in S0:
        inS[x] = True
        cur.append(x)
        for t in nb[x]:
            load[t] += 1
    best = list(cur)

    def fits(x):
        return all(load[t] < s for t in nb[x])

    def add(x):
        inS[x] = True
        for t in nb[x]:
            load[t] += 1

    def rem(x):
        inS[x] = False
        for t in nb[x]:
            load[t] -= 1

    for it in range(iters):
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        if fits(x):
            add(x)
            cur.append(x)
            if len(cur) > len(best):
                best = list(cur)
            continue
        if not cur:
            continue
        idx = rng.randrange(len(cur))
        r = cur[idx]
        rem(r)
        if fits(x):
            add(x)
            cur[idx] = x
        else:
            add(r)
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _best_load_set(nb, m, s, rng, deadline, conic=None):
    """Best load-bounded set from greedy + local search, or the conic if larger."""
    g = _greedy_load(nb, m, s, rng, 30, deadline)
    best = _improve_load(nb, m, s, g, rng, deadline, 2000)
    if conic is not None and len(conic) > len(best) and _load_ok(conic, nb, m, s):
        best = list(conic)
    return best


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """PG incidence plus an A-vertex per point of SA and a B-vertex per line of SB."""
    na, nb_ = len(SA), len(SB)
    n = 2 * m + na + nb_
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_bases(d, deadline, rng):
    """Arc-extended PG(2, q) graphs for every prime power q with s = d - q - 1 >= 1."""
    out = []
    for q in range(2, d - 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index, _pts = _pg_data(q)
        conic = None
        if s >= 2:
            conic = _conic_set(q, index, lib.GF(q))
        SA = _best_load_set(pl, m, s, rng, deadline, conic)
        SB = _best_load_set(lp, m, s, rng, deadline, conic)
        if not SA and not SB:
            continue
        out.append(_arc_graph(m, edges, pl, lp, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generic diameter-preserving growth by cover.
#
# A new vertex v with neighbour set N keeps diameter <= D provided the balls of
# radius D-1 around N cover every vertex of the current graph. Growth only adds
# vertices, so the result stays bipartite with max degree d.
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


def _cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidates; None if it fails."""
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
        if randomize and best_g > 1 and rng.random() < 0.4:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr]
        i = rng.choice(opts) if randomize else opts[0]
        v = pool.pop(i)
        chosen.append(v)
        covered |= ball[v]
    return chosen if covered == full else None


def _grow_random(n, edges, d, D, deadline, rng, tries):
    """Repeatedly add a vertex covering the graph within radius D-1, until stuck."""
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
        sides = [0, 1]
        rng.shuffle(sides)
        added = False
        for c in sides:
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(tries):
                if time.monotonic() >= deadline:
                    break
                chosen = _cover(cands, ball, full, d, rng, attempt > 0)
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    bases = [(best_n, best[1])]
    if d >= 2:
        n6, e6 = lib.haar_graph(3, [0, 1])  # C6, diameter 3
        consider(n6, e6)
        bases.append((n6, e6))

    # Projective plane base for the largest prime power q with q + 1 <= d.
    qs = [q for q in range(2, d) if lib.is_prime_power(q)]
    if qs:
        m, edges, _pl, _lp, _idx, _pts = _pg_data(max(qs))
        consider(2 * m, edges)
        bases.append((2 * m, edges))

    # Arc-extended projective plane graphs (diameter 3), with independent A/B sets.
    for n_c, e_c in _arc_bases(d, start + 0.3 * time_limit,
                               random.Random(seed * 7919 + d)):
        consider(n_c, e_c)
        bases.append((n_c, e_c))

    # Generalized quadrangle base for D >= 4.
    if D >= 4:
        gqs = [q for q in range(2, min(d - 1, 7) + 1) if lib.is_prime_power(q)]
        if gqs:
            n_g, e_g = _gq_w(max(gqs))
            consider(n_g, e_g)
            bases.append((n_g, e_g))

    # Main phase: round-robin randomized cover growth from the largest bases.
    bases = [b for b in bases if b[0] >= 2]
    bases.sort(key=lambda b: -b[0])
    bases = bases[:4]
    if not bases:
        return best

    slice_len = max(1.0, 0.12 * time_limit)
    k = 0
    while time.monotonic() < deadline - 0.5:
        n0, e0 = bases[k % len(bases)]
        k += 1
        end = min(deadline, time.monotonic() + slice_len)
        n1, e1 = _grow_random(n0, e0, d, D, end, rng, 20)
        consider(n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
