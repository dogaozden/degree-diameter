import random
import time

import lib

# ----------------------------------------------------------------------------
# Greedy vertex growth with exact diameter-3 certificates.
#
# Starting graphs: arc-extended PG(2,q) graphs (multiset construction) and the
# plain PG(2,q) incidence graph. Each start is then grown one vertex at a time.
#
# To add a vertex x on side s with neighbour set N (all on side t = 1 - s),
# the graph stays diameter-3 iff:
#   (i)  the neighbourhoods of N cover every existing vertex of side s
#        (each such vertex is at distance 2 from x), and
#   (ii) the 2-balls of N on side t cover every existing vertex of side t
#        (distance 1 for members of N, distance 3 for the rest).
# Adding a vertex never shortens or removes paths, so existing distances
# survive. The search picks N by randomized greedy set cover with local
# repair, which allows arbitrary neighbourhoods, not only full lines or points.
# ----------------------------------------------------------------------------


def _pg_lines(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, list(edges), pl, lp


def _multi(m, s, nbr, rng, deadline):
    """Multiset of entries with every target hit at most s times (iterated greedy)."""
    order = list(range(m))

    def fill(S, load):
        rng.shuffle(order)
        for x in order:
            nb_ = nbr[x]
            while all(load[t] < s for t in nb_):
                S.append(x)
                for t in nb_:
                    load[t] += 1
        return S

    cur = fill([], [0] * m)
    best = list(cur)
    while time.monotonic() < deadline:
        S = list(cur)
        load = [0] * m
        for x in S:
            for t in nbr[x]:
                load[t] += 1
        for _ in range(min(rng.randint(1, 3), len(S))):
            i = rng.randrange(len(S))
            x = S.pop(i)
            for t in nbr[x]:
                load[t] -= 1
        S = fill(S, load)
        if len(S) >= len(cur):
            cur = S
            if len(cur) > len(best):
                best = list(cur)
    return best


def _arc_base(q, d, rng, deadline):
    """PG(2,q) plus arc-style A and B vertices using spare degree s = d - q - 1."""
    s = d - q - 1
    m, E, pl, lp = _pg_lines(q)
    now = time.monotonic()
    half = max(0.0, (deadline - now) / 2)
    SA = _multi(m, s, pl, rng, time.monotonic() + half)
    SB = _multi(m, s, lp, rng, time.monotonic() + half)
    na, nb = len(SA), len(SB)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in lp[j]:
            E.append((Q, b))
    return 2 * m + na + nb, E


class _G:
    """Mutable bipartite graph with bitmask neighbourhoods for fast cover tests."""

    def __init__(self, n, edges, d):
        self.d = d
        self.n = n
        self.adj = [[] for _ in range(n)]
        self.nb = [0] * n
        for u, v in edges:
            self.adj[u].append(v)
            self.adj[v].append(u)
            self.nb[u] |= 1 << v
            self.nb[v] |= 1 << u
        self.side = self._color()
        self.mask = [0, 0]
        for v in range(n):
            self.mask[self.side[v]] |= 1 << v

    def _color(self):
        col = [-1] * self.n
        for s in range(self.n):
            if col[s] != -1:
                continue
            col[s] = 0
            st = [s]
            while st:
                u = st.pop()
                for v in self.adj[u]:
                    if col[v] == -1:
                        col[v] = 1 - col[u]
                        st.append(v)
        return col

    def add(self, s, N):
        x = self.n
        self.n += 1
        self.adj.append(list(N))
        self.nb.append(0)
        self.side.append(s)
        bit = 1 << x
        m = 0
        for y in N:
            self.adj[y].append(x)
            self.nb[y] |= bit
            m |= 1 << y
        self.nb[x] = m
        self.mask[s] |= bit

    def find(self, s, rng, iters, deadline):
        """Return a neighbour list N on side 1-s making a new side-s vertex valid, or None."""
        t = 1 - s
        d = self.d
        full_s = self.mask[s]
        full_t = self.mask[t]
        E = [y for y in range(self.n) if self.side[y] == t and len(self.adj[y]) < d]
        if not E:
            return None
        CA = {}
        CB = {}
        for y in E:
            CA[y] = self.nb[y]
            c = 1 << y
            for a in self.adj[y]:
                c |= self.nb[a]
            CB[y] = c

        def cover(sel):
            ca = 0
            cb = 0
            for y in sel:
                ca |= CA[y]
                cb |= CB[y]
            return ca, cb

        def cost(sel):
            ca, cb = cover(sel)
            return (full_s & ~ca).bit_count() + (full_t & ~cb).bit_count()

        def greedy(sel):
            sel = list(sel)
            ca, cb = cover(sel)
            inset = set(sel)
            while len(sel) < d and (full_s & ~ca or full_t & ~cb):
                bestk = None
                besty = None
                for y in E:
                    if y in inset:
                        continue
                    g = (CA[y] & ~ca).bit_count() + (CB[y] & ~cb).bit_count()
                    if g == 0:
                        continue
                    k = (g, rng.random())
                    if bestk is None or k > bestk:
                        bestk = k
                        besty = y
                if besty is None:
                    break
                sel.append(besty)
                inset.add(besty)
                ca |= CA[besty]
                cb |= CB[besty]
            return sel

        sel = greedy([])
        c = cost(sel)
        it = 0
        while c > 0 and it < iters and time.monotonic() < deadline:
            it += 1
            trial = list(sel)
            if trial:
                for _ in range(min(len(trial), rng.randint(1, 2))):
                    trial.pop(rng.randrange(len(trial)))
            trial = greedy(trial)
            tc = cost(trial)
            if tc <= c:
                sel, c = trial, tc
        return sel if c == 0 and sel else None

    def edges(self):
        return self.n, [(u, v) for u in range(self.n) for v in self.adj[u] if u < v]


def _grow(G, rng, deadline, iters):
    """Repeatedly add valid vertices on either side until none can be found."""
    while time.monotonic() < deadline:
        order = [0, 1]
        rng.shuffle(order)
        grown = False
        for s in order:
            N = G.find(s, rng, iters, deadline)
            if N:
                G.add(s, N)
                grown = True
                break
        if not grown:
            break


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, 0.75 * time_limit - 1.0)
    deadline = t0 + budget
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

    if D == 2 or d < 3:
        return best

    qs = [q for q in range(2, d) if lib.is_prime_power(q)]
    if not qs:
        return best
    q0 = max(qs)
    n0, e0 = lib.projective_plane_incidence(q0)
    consider(n0, e0)
    if q0 == d - 1:
        return best  # no spare degree, PG(2,d-1) is already the record shape

    # Phase 1: arc-style starts with spare degree.
    arc_qs = [q for q in sorted(qs, reverse=True) if d - q - 1 >= 1][:3]
    starts = []
    arc_deadline = t0 + 0.3 * budget
    for idx, q in enumerate(arc_qs):
        now = time.monotonic()
        slot = max(0.0, (arc_deadline - now) / (len(arc_qs) - idx))
        n_a, e_a = _arc_base(q, d, rng, now + slot)
        consider(n_a, e_a)
        starts.append((n_a, e_a))
    starts.append((n0, e0))

    # Phase 2: grow each start with a share of the remaining time.
    for idx, (n_s, e_s) in enumerate(starts):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(starts) - idx)
        G = _G(n_s, e_s, d)
        _grow(G, rng, slice_end, 20)
        n_g, e_g = G.edges()
        consider(n_g, e_g)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
