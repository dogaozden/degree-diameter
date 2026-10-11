import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generic helpers
# ----------------------------------------------------------------------------

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
# Arc-extended projective plane graphs (diameter 3). Kept from the parent.
# ----------------------------------------------------------------------------

def _pg_data(q):
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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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


def _local_arc(m, s, point_lines, line_points, S0, rng, deadline):
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m
    S = []

    def add(P):
        inS[P] = True
        S.append(P)
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def remove(P):
        inS[P] = False
        S.remove(P)
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def blockers(P):
        satL = {L for L in point_lines[P] if cl[L] >= s}
        satQ = {Q for Q in line_points[P] if cp[Q] >= s}
        if not satL and not satQ:
            return []
        return [R for R in S
                if any(L in satL for L in point_lines[R])
                or any(Q in satQ for Q in line_points[R])]

    for P in S0:
        add(P)
    best = list(S)
    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        B = blockers(P)
        if not B:
            add(P)
        elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.1):
            for R in B:
                remove(R)
            add(P)
        else:
            continue
        if len(S) > len(best):
            best = list(S)
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
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


def _arc_extensions(d, deadline, rng, threshold):
    """Candidate (n, edges) graphs from PG(2,q) plus A/B vertices on a point set S."""
    qs = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1:
            continue
        m = q * q + q + 1
        kmax = s * m // (q + 1)
        if 2 * m + 2 * kmax <= threshold:
            continue
        qs.append((q, s))

    out = []
    for idx, (q, s) in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        q_deadline = now + share
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        F = lib.GF(q)
        cands = []
        cs = _conic_set(q, index, F)
        if _loads_ok(cs, s, m, point_lines, line_points):
            cands.append(cs)
        if s == 2 and q % 2 == 1 and cands:
            # A conic is a maximum arc for odd q, so it is already optimal here.
            S = cands[0]
        else:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 20,
                                     now + 0.3 * share))
            S0 = max(cands, key=len, default=[])
            if not _loads_ok(S0, s, m, point_lines, line_points):
                S0 = []
            S = _local_arc(m, s, point_lines, line_points, S0, rng, q_deadline)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# NEW: ruin-and-recreate local search with exact diameter checks.
#
# The graph keeps dead slots so removal is cheap. A "recreate" step inserts a
# new vertex of colour c whose neighbourhood is a set of spare-degree
# opposite-colour vertices whose radius-(D-1) balls cover every alive vertex.
# That condition is exactly what keeps the new vertex within distance D of
# everything, and adding a vertex never lengthens existing distances.
# A "ruin" step removes a few vertices, which can break distances, so every
# accepted state is re-checked with a full bitmask diameter test.
# Plateau moves (same order) are accepted, and rare downhill moves too.
# ----------------------------------------------------------------------------

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
        if randomize and rng.random() < 0.3:
            thr = max(1, best_g - 1)
        opts = [i for i, g in enumerate(gains) if g >= thr]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


class _Graph:
    def __init__(self, n, edges, d):
        self.d = d
        self.adj = [set() for _ in range(n)]
        for u, v in edges:
            self.adj[u].add(v)
            self.adj[v].add(u)
        self.alive = [True] * n
        self.color = _bipartition(n, [list(s) for s in self.adj])
        self.free = []
        self.count = n
        self.init_n = n

    def snapshot(self):
        return ([set(s) for s in self.adj], self.alive[:], self.color[:],
                self.free[:], self.count)

    def restore(self, snap):
        adj, alive, color, free, count = snap
        self.adj = [set(s) for s in adj]
        self.alive = alive[:]
        self.color = color[:]
        self.free = free[:]
        self.count = count

    def ball(self, r):
        N = len(self.adj)
        alive = self.alive
        ball = [(1 << v) if alive[v] else 0 for v in range(N)]
        for _ in range(r):
            new = ball[:]
            for v in range(N):
                if alive[v]:
                    x = ball[v]
                    for u in self.adj[v]:
                        x |= ball[u]
                    new[v] = x
            ball = new
        return ball

    def full_mask(self):
        m = 0
        for v, a in enumerate(self.alive):
            if a:
                m |= 1 << v
        return m

    def diam_ok(self, D):
        full = self.full_mask()
        ball = self.ball(D)
        return all((ball[v] & full) == full
                   for v in range(len(self.adj)) if self.alive[v])

    def remove(self, v):
        for u in self.adj[v]:
            self.adj[u].discard(v)
        self.adj[v] = set()
        self.alive[v] = False
        self.free.append(v)
        self.count -= 1

    def insert(self, c, chosen):
        if self.free:
            v = self.free.pop()
            self.color[v] = c
        else:
            v = len(self.adj)
            self.adj.append(set())
            self.alive.append(True)
            self.color.append(c)
        self.alive[v] = True
        for s in chosen:
            self.adj[v].add(s)
            self.adj[s].add(v)
        self.count += 1
        return v

    def try_insert(self, c, D, rng, randomize):
        full = self.full_mask()
        ball2 = self.ball(D - 1)
        cands = [s for s in range(len(self.adj))
                 if self.alive[s] and self.color[s] == 1 - c and len(self.adj[s]) < self.d]
        chosen = _greedy_cover(cands, ball2, full, self.d, rng, randomize)
        if chosen is None:
            return False
        self.insert(c, chosen)
        return True

    def export(self):
        ids = [v for v in range(len(self.adj)) if self.alive[v]]
        mp = {v: i for i, v in enumerate(ids)}
        edges = [(mp[u], mp[v]) for u in ids for v in self.adj[u] if u < v]
        return len(ids), edges


def _fill(g, D, rng):
    """Greedily insert vertices while the cover condition allows it."""
    for _ in range(200):
        progress = False
        for c in (0, 1):
            if g.try_insert(c, D, rng, False):
                progress = True
        if not progress:
            break


def _lns(g, D, deadline, rng):
    best = g.export()
    while time.monotonic() < deadline:
        snap = g.snapshot()
        before = g.count
        alive_ids = [v for v in range(len(g.adj)) if g.alive[v]]
        ext = [v for v in alive_ids if v >= g.init_n]
        pool = ext if (ext and rng.random() < 0.7) else alive_ids
        r = min(rng.choice([1, 1, 2, 2, 3]), len(pool))
        for v in rng.sample(pool, r):
            g.remove(v)
        target = r + (1 if rng.random() < 0.3 else 0)
        added = 0
        tries = 0
        while added < target and tries < 8:
            tries += 1
            c = rng.randrange(2)
            if g.try_insert(c, D, rng, True) or g.try_insert(1 - c, D, rng, True):
                added += 1
        if g.diam_ok(D) and (g.count >= before or rng.random() < 0.01):
            if g.count > best[0]:
                best = g.export()
        else:
            g.restore(snap)
    return best


def _saturate_edges(n, edges, d, rng):
    """Join deficient opposite-side vertices. Adding edges never breaks diameter."""
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


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

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

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    base = None
    if D == 3:
        base = _best_pg(d)
    elif D == 4:
        base = _best_gq(d)
    if base is not None:
        consider(*base)

    if D == 3:
        threshold = base[0] if base is not None else best[0]
        for n_c, e_c in _arc_extensions(d, start + 0.12 * time_limit,
                                        random.Random(seed * 7919 + d), threshold):
            consider(n_c, e_c)

    # Calibration cases already at the Moore bound need no search.
    if best[0] >= lib.moore_bound(d, D):
        return best

    if best[0] > 2:
        g = _Graph(best[0], best[1], d)
        _fill(g, D, rng)
        n_l, e_l = _lns(g, D, deadline, rng)
        e_l = _saturate_edges(n_l, e_l, d, rng)
        consider(n_l, e_l)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
