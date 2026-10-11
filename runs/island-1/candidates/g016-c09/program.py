import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Parent constructions kept as safe seeds: projective planes, Araujo-Pardo-Lopez,
# W(q) generalized quadrangles, arc extensions and cover-based growth.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_best(d):
    """Araujo-Pardo-Lopez graph for the largest prime power q <= d - 2."""
    for q in range(min(d - 2, 23), 2, -1):
        if lib.is_prime_power(q):
            try:
                return lib.araujo_lopez_graph(q)
            except ValueError:
                return None
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


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


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
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


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
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


def _arc_extensions(d, deadline, rng):
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


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


def _extend_cover(n, edges, d, D, deadline, rng):
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


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices first, then saturate edges with leftover spare degree."""
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


def _bad_count(n, adj, D):
    """Number of ordered vertex pairs at distance > D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _insert_and_repair(n, edges, d, D, deadline, rng, tries=3, anneal_iters=300):
    """Return (n+2, edges) with diameter <= D, or None if repair fails in time."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _bipartition(n, [list(s) for s in adj])
    Eo = [(u, v) if col[u] == 0 else (v, u) for u, v in edges]

    best_state = None
    best_c = None
    for _ in range(tries):
        if time.monotonic() >= deadline:
            break
        rng.shuffle(Eo)
        used_a, used_b, pick = set(), set(), []
        for a, b in Eo:
            if a not in used_a and b not in used_b:
                pick.append((a, b))
                used_a.add(a)
                used_b.add(b)
                if len(pick) == d:
                    break
        if len(pick) < d:
            continue
        adj2 = [set(s) for s in adj] + [set(), set()]
        x, y = n, n + 1
        for a, b in pick:
            adj2[a].discard(b)
            adj2[b].discard(a)
            adj2[x].add(b)
            adj2[b].add(x)
            adj2[y].add(a)
            adj2[a].add(y)
        c = _bad_count(n + 2, adj2, D)
        if best_c is None or c < best_c:
            best_c, best_state = c, adj2
        if best_c == 0:
            break
    if best_state is None:
        return None

    n2 = n + 2
    adj2 = best_state
    c = best_c
    col2 = col + [0, 1]
    E = [[a, b] for a in range(n2) if col2[a] == 0 for b in adj2[a]]
    if len(E) < 2:
        return None

    for it in range(anneal_iters):
        if c == 0 or time.monotonic() >= deadline:
            break
        i, j = rng.sample(range(len(E)), 2)
        a, b = E[i]
        cc, dd = E[j]
        if a == cc or b == dd or dd in adj2[a] or b in adj2[cc]:
            continue
        adj2[a].discard(b)
        adj2[b].discard(a)
        adj2[cc].discard(dd)
        adj2[dd].discard(cc)
        adj2[a].add(dd)
        adj2[dd].add(a)
        adj2[cc].add(b)
        adj2[b].add(cc)
        c2 = _bad_count(n2, adj2, D)
        T = 4.0 * (0.05 ** (it / anneal_iters))
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            E[i] = [a, dd]
            E[j] = [cc, b]
            c = c2
        else:
            adj2[a].discard(dd)
            adj2[dd].discard(a)
            adj2[cc].discard(b)
            adj2[b].discard(cc)
            adj2[a].add(b)
            adj2[b].add(a)
            adj2[cc].add(dd)
            adj2[dd].add(cc)

    if c != 0:
        return None
    out = [(a, b) for a in range(n2) if col2[a] == 0 for b in adj2[a]]
    return n2, out


def _repair_growth(n, edges, d, D, deadline, rng, consider):
    """Repeatedly insert vertex pairs with repair; stop after 3 consecutive failures."""
    fails = 0
    while time.monotonic() < deadline and fails < 3:
        res = _insert_and_repair(n, edges, d, D, deadline, rng)
        if res is None:
            fails += 1
            continue
        fails = 0
        n, edges = res
        consider(n, edges)
    return n, edges


# ----------------------------------------------------------------------------
# NEW construction for D >= 4: annealed d-regular bipartite graphs.
#
# Start from the circulant (Haar-type) bipartite graph with shifts 0..d-1, which
# is simple and d-regular. Then anneal over degree-preserving 2-switches
# (a,b),(c,e) -> (a,e),(c,b) on one side's slots, minimizing the number of
# ordered pairs at distance > D. Distances come from packed-bit BFS with numpy.
# The side size N is searched by bisection between a lower bound (2N > current
# best order) and the Moore bound.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


class _RegState:
    """d-regular bipartite graph with sides of size N; side-0 vertex a is index a, side-1 vertex b is index N+b."""

    def __init__(self, N, d, D):
        self.N = N
        self.d = d
        self.D = D
        self.n = 2 * N
        self.eye = np.packbits(np.eye(self.n, dtype=bool), axis=1)
        self.nbr0 = np.array([[(a + j) % N for j in range(d)] for a in range(N)], dtype=np.int64)
        self.nbr1 = np.array([[(b - j) % N for j in range(d)] for b in range(N)], dtype=np.int64)

    def cost(self):
        """Number of ordered pairs at distance > D."""
        comb = np.vstack((self.N + self.nbr0, self.nbr1))
        reach = self.eye
        for _ in range(self.D):
            new = reach.copy()
            for j in range(self.d):
                np.bitwise_or(new, reach[comb[:, j]], out=new)
            reach = new
        return self.n * self.n - int(_POP8[reach].sum())

    def _rep1(self, v, old, new):
        row = self.nbr1[v]
        k = np.flatnonzero(row == old)[0]
        row[k] = new

    def propose(self, rng):
        N, d = self.N, self.d
        a = rng.randrange(N)
        c = rng.randrange(N)
        if a == c:
            return None
        i = rng.randrange(d)
        j = rng.randrange(d)
        b = int(self.nbr0[a, i])
        e = int(self.nbr0[c, j])
        if b == e:
            return None
        if np.any(self.nbr0[a] == e) or np.any(self.nbr0[c] == b):
            return None
        return (a, i, b, c, j, e)

    def move(self, a, i, b, c, j, e):
        # Old edges a-b, c-e; new edges a-e, c-b.
        self.nbr0[a, i] = e
        self.nbr0[c, j] = b
        self._rep1(b, a, c)
        self._rep1(e, c, a)

    def undo(self, a, i, b, c, j, e):
        self.nbr0[a, i] = b
        self.nbr0[c, j] = e
        self._rep1(b, c, a)
        self._rep1(e, a, c)

    def edges(self):
        out = []
        for a in range(self.N):
            for i in range(self.d):
                out.append((a, self.N + int(self.nbr0[a, i])))
        return self.n, out


def _anneal_regular(N, d, D, deadline, rng):
    """Anneal a d-regular bipartite graph with side N to diameter <= D; None on timeout."""
    st = _RegState(N, d, D)
    cost = st.cost()
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 5.0, 0.2
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        mv = st.propose(rng)
        if mv is None:
            continue
        st.move(*mv)
        c2 = st.cost()
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            st.undo(*mv)
    return st if cost == 0 else None


def _regular_search(d, D, best_n, deadline, rng, consider):
    """Bisect the side size N for which the annealed regular graph reaches diameter <= D."""
    if d < 3 or D < 4:
        return
    lo = max(best_n // 2 + 1, d)
    hi = lib._moore_bound(d, D) // 2
    if lo > hi:
        return
    ok = None
    fail = None
    N = lo
    while True:
        now = time.monotonic()
        if now >= deadline - 0.05:
            break
        if ok is not None and fail is not None and fail - ok <= 1:
            break
        N = min(max(N, d), hi)
        budget = max(0.5, (deadline - now) * 0.4)
        st = _anneal_regular(N, d, D, min(deadline, now + budget), rng)
        if st is not None:
            n, e = st.edges()
            consider(n, e)
            ok = N if ok is None else max(ok, N)
            if fail is None:
                if N >= hi:
                    break
                N = min(hi, int(N * 1.15) + 1)
            else:
                N = (ok + fail) // 2
        else:
            fail = N if fail is None else min(fail, N)
            if ok is None:
                if N <= d:
                    break
                N = max(d, int(N * 0.95))
            else:
                N = (ok + fail) // 2


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    if D >= 3:
        ara = _araujo_best(d)
        if ara is not None:
            consider(ara[0], ara[1])
            n2, e2 = _grow(ara[0], ara[1], d, D, start + 0.15 * time_limit, rng)
            consider(n2, e2)
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.25 * time_limit, rng)
            consider(n2, e2)
        for n_c, e_c in _arc_extensions(d, start + 0.30 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.35 * time_limit, rng)
            consider(n2, e2)

    if D == 3 and best_n >= 2 and time.monotonic() < start + 0.75 * time_limit:
        rng3 = random.Random(seed * 1000003 + d * 17 + D)
        _repair_growth(best_n, list(best[1]), d, D, start + 0.75 * time_limit, rng3, consider)

    if D >= 4:
        rng4 = random.Random(seed * 104729 + d * 31 + D)
        _regular_search(d, D, best_n, start + 0.80 * time_limit, rng4, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
