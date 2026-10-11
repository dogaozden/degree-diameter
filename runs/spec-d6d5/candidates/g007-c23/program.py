import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic bases (safe starting points).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q) (diameter 4)."""
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


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Cover-based growth and saturation (diameter-preserving).
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
            for attempt in range(60):
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
    for _ in range(6):
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
# New family: bi-Cayley (Haar-type) graphs over semidirect products Z_m x| Z_k.
#
# Vertices A_g = g and B_x = N + x for g, x in G (|G| = N). Connection set
# S = {s_1..s_d} subset of G gives edges A_g -- B_{g*s} for all s in S.
# Left translation by h is an automorphism (A_g -> A_{hg}, B_x -> B_{hx}),
# so it is transitive on each side. Hence the graph has diameter <= D iff
# every vertex is within D of A_e and of B_e. The search is a hill-climb
# over S using this two-source BFS cost, which is far cheaper than an
# all-pairs check.
# ----------------------------------------------------------------------------

def _group_candidates(N):
    """(m, k, r) with m*k = N giving the semidirect product Z_m x| Z_k (k=1 is cyclic)."""
    out = []
    for k in range(1, N + 1):
        if N % k or N // k < 2:
            continue
        m = N // k
        if k == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


class _Group:
    def __init__(self, m, k, r):
        self.N, self.mul, self.inv = lib.semidirect_group(m, k, r)
        self._R = {}

    def right(self, s):
        """List g -> g*s over all group elements (cached)."""
        R = self._R.get(s)
        if R is None:
            mul = self.mul
            R = [mul(g, s) for g in range(self.N)]
            self._R[s] = R
        return R


def _adj(grp, S):
    N = grp.N
    adj = [[] for _ in range(2 * N)]
    for s in S:
        R = grp.right(s)
        for g in range(N):
            x = N + R[g]
            adj[g].append(x)
            adj[x].append(g)
    return adj


def _cost(N, adj, D):
    """Vertices not reached within D from A_e (vertex 0) and from B_e (vertex N). Zero means valid."""
    total_n = 2 * N
    total = 0
    for src in (0, N):
        seen = bytearray(total_n)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += total_n - cnt
    return total


def _edges(grp, S):
    N = grp.N
    E = []
    for s in S:
        R = grp.right(s)
        E.extend((g, N + R[g]) for g in range(N))
    return 2 * N, E


def _search(grp, d, D, rng, deadline):
    """Hill-climb a d-element connection set S with diameter <= D; returns S or None."""
    N = grp.N
    if d > N:
        return None
    while time.monotonic() < deadline:
        S = rng.sample(range(N), d)
        c = _cost(N, _adj(grp, S), D)
        stall = 0
        while c > 0 and stall < 300 and time.monotonic() < deadline:
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in S:
                stall += 1
                continue
            T = S[:]
            T[i] = x
            ct = _cost(N, _adj(grp, T), D)
            if ct <= c:
                stall = 0 if ct < c else stall + 1
                S, c = T, ct
            else:
                stall += 1
                if rng.random() < 0.02:
                    S, c = T, ct
        if c == 0:
            return S
    return None


def _cayley_search(d, D, best_n, rng, deadline, consider):
    """Search group orders N (so the graph has 2N vertices) above the current best."""
    moore = lib._moore_bound(d, D)
    lo = max(d, 4, best_n // 2 + 1)
    while time.monotonic() < deadline:
        hi = min(moore // 2, max(lo + 4, moore // 4))
        if lo > hi:
            break
        N = lo + int((hi - lo) * rng.random() ** 2)
        cands = _group_candidates(N)
        if not cands:
            lo = N + 1
            continue
        m, k, r = rng.choice(cands)
        grp = _Group(m, k, r)
        att_deadline = min(deadline, time.monotonic() + 2.5)
        S = _search(grp, d, D, rng, att_deadline)
        if S is not None:
            n, e = _edges(grp, S)
            consider(n, e)
            lo = max(lo, N + 1)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

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
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.1 * time_limit, rng)
            consider(n2, e2)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.18 * time_limit, rng)
            consider(n2, e2)

    # Main new search: bi-Cayley graphs over semidirect products, hill-climbed
    # on the two-source diameter cost.
    if D >= 3:
        _cayley_search(d, D, best_n, rng, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
