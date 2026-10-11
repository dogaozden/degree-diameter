import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Time fractions (of time_limit). For D >= 5 the lift/growth stage ends early and
# the rest goes to a regular-graph insertion + annealing search (new family).
# ----------------------------------------------------------------------------
FRAC_LIFT = 0.72
FRAC_TOTAL = 0.85
FRAC_LIFT_LONG = 0.35
FRAC_GROW_LONG = 0.45
GQ_Q_MAX = 9
ARC_Q_MAX = 23


# ----------------------------------------------------------------------------
# Algebraic bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph for degree d when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
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
    """W(q) for the largest prime power q <= min(d - 1, GQ_Q_MAX)."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
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


def _local_improve(m, s, point_lines, line_points, S, rng, deadline, iters):
    """Plateau-walking 1-swap local search that grows a feasible load-bounded set S."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m

    def add(P):
        inS[P] = True
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def rem(P):
        inS[P] = False
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def fits(P):
        return (all(cl[L] < s for L in point_lines[P])
                and all(cp[Q] < s for Q in line_points[P]))

    cur = list(S)
    for P in cur:
        add(P)
    best = list(cur)
    for it in range(iters):
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        if fits(P):
            add(P)
            cur.append(P)
            if len(cur) > len(best):
                best = list(cur)
            continue
        if not cur:
            continue
        idx = rng.randrange(len(cur))
        R = cur[idx]
        rem(R)
        if fits(P):
            add(P)
            cur[idx] = P
        else:
            add(R)
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
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
    for q in range(2, min(d - 1, ARC_Q_MAX) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            g = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
            g = _local_improve(m, s, point_lines, line_points, g, rng, deadline, 3000)
            cands.append(g)
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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of the graph."""
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
    """Extend by cover vertices, then saturate edges with the leftover spare degree."""
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


def _grow_best(n, edges, d, D, deadline, rng, tries=2):
    """Several randomized growth runs, keeping the largest result."""
    best = (n, list(edges))
    for t in range(tries):
        now = time.monotonic()
        if now >= deadline:
            break
        per = now + (deadline - now) / (tries - t)
        c = _grow(n, edges, d, D, per, rng)
        if c[0] > best[0]:
            best = c
    return best


# ----------------------------------------------------------------------------
# NEW family for D >= 5: regular bipartite graphs grown by pair insertion and
# repaired by simulated annealing on double-edge switches.
#
# State: a d-regular bipartite graph with sides A (colour 0) and B (colour 1).
# Insertion: pick d edges (a_t, b_t) with pairwise distinct endpoints, delete
# them, add a new A-vertex x adjacent to every b_t and a new B-vertex y adjacent
# to every a_t. Degrees stay exactly d, and the order grows by 2.
# Repair: switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) keep degrees and
# bipartiteness; cost = number of unordered vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _is_regular(n, edges, d):
    """True if every vertex of the graph has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


class _RegSA:
    """Regular bipartite graph with edge list E of (a, b), a in side 0, b in side 1."""

    def __init__(self, n, E, color, d, D):
        self.n = n
        self.E = list(E)
        self.color = list(color)
        self.d = d
        self.D = D
        self._rebuild()

    def _rebuild(self):
        self.adj = [[] for _ in range(self.n)]
        self.has = set()
        for a, b in self.E:
            self.adj[a].append(b)
            self.adj[b].append(a)
            self.has.add((a, b))

    def snapshot(self):
        return (self.n, list(self.E), list(self.color))

    def restore(self, snap):
        self.n, E, color = snap
        self.E = list(E)
        self.color = list(color)
        self._rebuild()

    def cost(self):
        """Number of unordered vertex pairs at distance greater than D (unreachable counts)."""
        n = self.n
        adj = self.adj
        reach = [1 << v for v in range(n)]
        for _ in range(self.D):
            new = [0] * n
            for v in range(n):
                r = reach[v]
                for u in adj[v]:
                    r |= reach[u]
                new[v] = r
            if new == reach:
                break
            reach = new
        return sum(n - r.bit_count() for r in reach) // 2

    def can_switch(self, i, j):
        a1, b1 = self.E[i]
        a2, b2 = self.E[j]
        return (a1 != a2 and b1 != b2
                and (a1, b2) not in self.has and (a2, b1) not in self.has)

    def switch(self, i, j):
        """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Calling it again on the same
        indices reverts the move, because the new pairs have the same shape."""
        a1, b1 = self.E[i]
        a2, b2 = self.E[j]
        self.E[i] = (a1, b2)
        self.E[j] = (a2, b1)
        self.has.discard((a1, b1))
        self.has.discard((a2, b2))
        self.has.add((a1, b2))
        self.has.add((a2, b1))
        adj = self.adj
        adj[a1].remove(b1)
        adj[a1].append(b2)
        adj[b2].remove(a2)
        adj[b2].append(a1)
        adj[a2].remove(b2)
        adj[a2].append(b1)
        adj[b1].remove(a1)
        adj[b1].append(a2)

    def insert_pair(self, rng):
        """Insert a new (A, B) vertex pair as described above. Returns False if no d-matching exists."""
        d = self.d
        E = self.E
        idx = list(range(len(E)))
        rng.shuffle(idx)
        used_a = set()
        used_b = set()
        chosen = []
        for k in idx:
            a, b = E[k]
            if a in used_a or b in used_b:
                continue
            used_a.add(a)
            used_b.add(b)
            chosen.append(k)
            if len(chosen) == d:
                break
        if len(chosen) < d:
            return False
        x = self.n
        y = self.n + 1
        self.n += 2
        self.color.append(0)
        self.color.append(1)
        cs = set(chosen)
        newE = [e for k, e in enumerate(E) if k not in cs]
        for k in chosen:
            a, b = E[k]
            newE.append((x, b))
            newE.append((a, y))
        self.E = newE
        self._rebuild()
        return True

    def anneal(self, rng, cost, iters, deadline):
        """Annealing over switches. Returns True as soon as the cost reaches zero."""
        T0 = 1.5
        T1 = 0.2
        m = len(self.E)
        for it in range(iters):
            if (it & 15) == 0 and time.monotonic() > deadline:
                return False
            T = T0 * (T1 / T0) ** (it / max(1, iters))
            i = rng.randrange(m)
            j = rng.randrange(m)
            if i == j or not self.can_switch(i, j):
                continue
            self.switch(i, j)
            c2 = self.cost()
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
                if cost == 0:
                    return True
            else:
                self.switch(i, j)
        return False


def _insertion_stage(d, D, base, rng, deadline, consider):
    """Grow a regular valid graph by pair insertion, repairing each step with annealing."""
    n, edges = base
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)
    if any(c < 0 for c in color):
        return
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    st = _RegSA(n, E, color, d, D)
    snap = st.snapshot()
    iters = 300
    fails = 0
    while time.monotonic() < deadline:
        if not st.insert_pair(rng):
            continue
        c = st.cost()
        ok = (c == 0) or st.anneal(rng, c, iters, deadline)
        if ok:
            snap = st.snapshot()
            consider((st.n, [(a, b) for a, b in st.E]))
            fails = 0
            iters = 300
        else:
            st.restore(snap)
            fails += 1
            if fails % 4 == 0:
                iters = min(iters * 2, 8000)


# ----------------------------------------------------------------------------
# Group voltage lifts over Z_m x| Z_k2, annealed (parent family, used for all D).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost_lift(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges_lift(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost_lift(k, G, D, darts, perms)

    if cost < _BIG:
        T0 = max(1.0, 0.05 * cost)
    else:
        T0 = 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost_lift(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost_lift(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges_lift(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Haar graph hill-climb (small D, secondary family).
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    long_d = D >= 5
    lift_frac = FRAC_LIFT_LONG if long_d else FRAC_LIFT
    deadline = start + lift_frac * time_limit
    final_deadline = start + (FRAC_GROW_LONG if long_d else FRAC_TOTAL) * time_limit
    sa_deadline = start + FRAC_TOTAL * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D                       # even cycle: bipartite, diameter D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # K_{d,d} has diameter 2 and is the always-valid fallback.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best = fallback
    pool = [fallback]
    bases = [fallback]
    moore = lib._moore_bound(d, D)

    def consider(c):
        nonlocal best
        if c is None:
            return
        n, e = c
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            pool.append(best)
            pool.sort(key=lambda item: -item[0])
            del pool[4:]

    # Algebraic bases.
    if D >= 3:
        ap = _araujo(d)
        if ap is not None:
            bases.append(ap)
            consider(ap)
            if ap[0] >= moore:
                return best
            consider(_grow(ap[0], ap[1], d, D, start + 0.12 * time_limit, rng))
        pg = _best_pg(d)
        if pg is not None:
            bases.append(pg)
            consider(pg)
            if pg[0] >= moore:
                return best
            consider(_grow(pg[0], pg[1], d, D, start + 0.2 * time_limit, rng))
        for c in _arc_extensions(d, start + 0.3 * time_limit,
                                 random.Random(seed * 7919 + d)):
            consider(c)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            bases.append(gq)
            consider(gq)
            if gq[0] >= moore:
                return best
            consider(_grow(gq[0], gq[1], d, D, start + 0.35 * time_limit, rng))

    # Lift search (parent family).
    try:
        if D >= 5:
            ks = [1, 1, 2, 2, 3, 4]
            anneal_iters = 1500
        else:
            ks = [1, 2, 2, 3, 4]
            anneal_iters = 400
        haar_m, haar_miss = d + 1, 0
        while time.monotonic() < deadline and best[0] < moore:
            if D <= 4 and haar_miss < 4 and 2 * haar_m <= moore and rng.random() < 0.1:
                S = _search_haar(d, D, haar_m, rng, deadline, 120)
                if S is not None:
                    consider(lib.haar_graph(haar_m, S))
                    haar_miss = 0
                else:
                    haar_miss += 1
                haar_m += 1
                continue

            k = rng.choice(ks)
            base = best[0] // (2 * k)
            if D >= 5:
                G = max(2, base + 1 + rng.randrange(0, 3))
            else:
                G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal_lift(d, D, k, order, mul, rng, deadline, anneal_iters)
            if res is not None:
                consider(res)
    except Exception:
        pass

    # Final growth of the top candidates.
    try:
        top = sorted(pool, key=lambda c: -c[0])[:3]
        for idx, c in enumerate(top):
            now = time.monotonic()
            if now >= final_deadline:
                break
            slice_end = now + (final_deadline - now) / (len(top) - idx)
            consider(_grow_best(c[0], c[1], d, D, slice_end, rng, tries=2))
    except Exception:
        pass

    # New family (D >= 5): insertion + annealing from the largest regular valid base.
    if long_d and time.monotonic() < sa_deadline:
        try:
            regs = [c for c in (pool + bases)
                    if c is not None and c[0] > 0 and _is_regular(c[0], c[1], d)]
            if regs:
                start_c = max(regs, key=lambda c: c[0])
                _insertion_stage(d, D, start_c, rng, sa_deadline, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
