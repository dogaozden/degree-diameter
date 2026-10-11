import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graph: generalized quadrangle W(q) incidence graph (diameter 4).
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


# ----------------------------------------------------------------------------
# Fallback growth: cover-based vertex addition (keeps diameter, degree, bipartiteness).
# ----------------------------------------------------------------------------

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
    adj = _adjacency(n, edges)
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
            for attempt in range(100):
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
    """Add edges between non-adjacent opposite-side vertices with spare degree (never hurts diameter)."""
    edges = list(edges)
    adj = _adjacency(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
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
# Main new construction: bipartite voltage lifts over (non-abelian) finite groups.
#
# Base graph: k A-vertices and k B-vertices, joined by d perfect-matching layers
# (so every base vertex has degree d). Each dart (i, j, g) lifts to the edges
# (A_i, x) -- (B_j, x*g) for all x in G. Left multiplication by G is an
# automorphism of the lift, so the diameter is at most D iff every base vertex
# reaches the whole lift within D steps from its identity lift vertex.
# Voltages are found by hill climbing on the number of unreached pairs.
# ----------------------------------------------------------------------------

def _groups(M, rng):
    """Multiplications of order M: the cyclic group plus one random semidirect product Z_m x| Z_k."""
    out = [lambda x, g, M=M: (x + g) % M]
    opts = []
    for kk in range(2, M + 1):
        if M % kk:
            continue
        m = M // kk
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                opts.append((m, kk, r))
    rng.shuffle(opts)
    for m, kk, r in opts[:1]:
        out.append(lib.semidirect_group(m, kk, r)[1])
    return out


def _score(N, k, M, mul, darts, D):
    """Return (number of (source, vertex) pairs unreached within D, adjacency sets)."""
    adj = [set() for _ in range(N)]
    for i, j, g in darts:
        base_b = (k + j) * M
        for x in range(M):
            a = i * M + x
            b = base_b + mul(x, g)
            adj[a].add(b)
            adj[b].add(a)
    bad = 0
    for i in range(2 * k):
        src = i * M
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                for u in adj[v]:
                    if not seen[u]:
                        seen[u] = True
                        nxt.append(u)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        bad += N - count
    return bad, adj


class _Climb:
    """Persistent hill-climbing state for one (k, group) combination."""

    def __init__(self, k, M, mul, d, D, rng):
        self.k, self.M, self.mul, self.d, self.D, self.rng = k, M, mul, d, D, rng
        self.N = 2 * k * M
        self.restart()

    def restart(self):
        rng = self.rng
        darts = []
        for _ in range(self.d):
            perm = list(range(self.k))
            rng.shuffle(perm)
            for i in range(self.k):
                darts.append([i, perm[i], rng.randrange(self.M)])
        self.darts = darts
        self.cur, self.adj = _score(self.N, self.k, self.M, self.mul, darts, self.D)
        self.stale = 0

    def run(self, steps):
        rng = self.rng
        for _ in range(steps):
            if self.cur == 0:
                return True
            idx = rng.randrange(len(self.darts))
            old = self.darts[idx][2]
            new = rng.randrange(self.M)
            if new == old:
                continue
            self.darts[idx][2] = new
            val, adj = _score(self.N, self.k, self.M, self.mul, self.darts, self.D)
            if val <= self.cur or rng.random() < 0.01:
                self.stale = self.stale + 1 if val >= self.cur else 0
                self.cur, self.adj = val, adj
            else:
                self.darts[idx][2] = old
                self.stale += 1
            if self.stale > 300:
                self.restart()
        return self.cur == 0

    def edges(self):
        return [(a, b) for a in range(self.N) for b in self.adj[a] if a < b]


def _lift_search(d, D, moore, best_n, rng, deadline):
    """Round-robin hill climbing over lifts with more than best_n vertices. Returns (n, edges) or None."""
    climbers = []
    for k in (1, 2):
        hi = moore // (2 * k)
        lo = best_n // (2 * k) + 1
        if hi < lo or hi < 2:
            continue
        span = hi - lo
        count = min(span + 1, 30)
        ms = {hi - (span * t) // max(1, count - 1) for t in range(count)}
        for M in sorted(ms, reverse=True):
            if M < 2:
                continue
            for mul in _groups(M, rng):
                climbers.append(_Climb(k, M, mul, d, D, rng))
    if not climbers:
        return None

    best = None
    cur = best_n
    while time.monotonic() < deadline:
        active = [c for c in climbers if c.N > cur]
        if not active:
            break
        for c in active:
            if time.monotonic() >= deadline:
                break
            if c.N <= cur:
                continue
            if c.run(40):
                edges = c.edges()
                if lib.is_valid(c.N, edges, d, D):
                    cur = c.N
                    best = (c.N, edges)
                else:
                    c.restart()
    return best


# ----------------------------------------------------------------------------
# Driver.
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

    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    bases = []
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                bases.append(lib.projective_plane_incidence(q))
                break
    elif D >= 4:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            bases.append(_gq_w(q))

    for b in bases:
        consider(b[0], b[1])
    if best[0] >= moore:
        return best

    # Short fallback growth so a valid, reasonably large graph is always in hand.
    grow_deadline = start + 0.25 * (deadline - start)
    for b in bases:
        if time.monotonic() >= grow_deadline:
            break
        n2, e2 = _grow(b[0], b[1], d, D, grow_deadline, rng)
        consider(n2, e2)
    if best[0] >= moore:
        return best

    # Main phase: voltage-lift search over non-abelian groups.
    try:
        found = _lift_search(d, D, moore, best[0], rng, deadline)
    except Exception:
        found = None
    if found is not None:
        consider(found[0], found[1])

    return best
