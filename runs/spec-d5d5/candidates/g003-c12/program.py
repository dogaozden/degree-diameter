import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (valid for any D they are checked against).
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bold new family: direct simulated annealing on bipartite graphs.
#
# A d-regular bipartite graph on s + s vertices is improved by degree-preserving
# edge switches, minimising the number of ordered vertex pairs at distance > D.
# Once a zero-cost graph is found, one new A-vertex and one new B-vertex are
# added by splicing d existing edges, which keeps every degree at exactly d, and
# the search continues from that warm start.
#
# Ids: A-vertex i -> 2i, B-vertex j -> 2j+1, so ids stay compact as s grows.
# ----------------------------------------------------------------------------

def _cost_bip(adj, D):
    """Ordered pairs (u, v) with dist(u, v) > D, via bitmask balls."""
    n = len(adj)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


class _Bip:
    def __init__(self):
        self.ea = []
        self.eb = []
        self.S = set()
        self.adj = []

    def _add_edge(self, a, b):
        self.ea.append(a)
        self.eb.append(b)
        self.S.add((a, b))
        self.adj[a].append(b)
        self.adj[b].append(a)

    def _set_edge(self, i, a, b):
        oa, ob = self.ea[i], self.eb[i]
        self.adj[oa].remove(ob)
        self.adj[ob].remove(oa)
        self.S.discard((oa, ob))
        self.ea[i] = a
        self.eb[i] = b
        self.S.add((a, b))
        self.adj[a].append(b)
        self.adj[b].append(a)

    def init_regular(self, s, d, rng):
        """Random d-regular bipartite graph with s vertices per side (union of d perfect matchings)."""
        self.adj = [[] for _ in range(2 * s)]
        for _layer in range(d):
            for _ in range(200):
                p = list(range(s))
                rng.shuffle(p)
                if all((2 * i, 2 * p[i] + 1) not in self.S for i in range(s)):
                    break
            else:
                return False
            for i in range(s):
                self._add_edge(2 * i, 2 * p[i] + 1)
        return True

    def grow(self, d, rng):
        """Add one A-vertex and one B-vertex, each of degree d, by splicing d edges.

        Edge (x, y) with distinct x's and distinct y's becomes (x, new_B), and
        (new_A, y) is added. Every existing degree is unchanged.
        """
        s = len(self.adj) // 2
        order = list(range(len(self.ea)))
        rng.shuffle(order)
        used_a, used_b, picks = set(), set(), []
        for i in order:
            if self.ea[i] not in used_a and self.eb[i] not in used_b:
                picks.append(i)
                used_a.add(self.ea[i])
                used_b.add(self.eb[i])
                if len(picks) == d:
                    break
        if len(picks) < d:
            return False
        na, nb = 2 * s, 2 * s + 1
        self.adj.append([])
        self.adj.append([])
        for i in picks:
            x, y = self.ea[i], self.eb[i]
            self._set_edge(i, x, nb)
            self._add_edge(na, y)
        return True

    def anneal(self, D, rng, deadline, t0, t1):
        """Switch-based annealing; returns True once the cost is zero, False on timeout."""
        m = len(self.ea)
        cost = _cost_bip(self.adj, D)
        if cost == 0:
            return True
        start = time.monotonic()
        span = max(1e-3, deadline - start)
        T = t0
        it = 0
        while True:
            if it % 8 == 0:
                now = time.monotonic()
                if now >= deadline:
                    return False
                frac = min(1.0, (now - start) / span)
                T = t0 * (t1 / t0) ** frac
            it += 1
            i = rng.randrange(m)
            j = rng.randrange(m)
            a1, b1 = self.ea[i], self.eb[i]
            a2, b2 = self.ea[j], self.eb[j]
            if a1 == a2 or b1 == b2 or (a1, b2) in self.S or (a2, b1) in self.S:
                continue
            self._set_edge(i, a1, b2)
            self._set_edge(j, a2, b1)
            c2 = _cost_bip(self.adj, D)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
                if cost == 0:
                    return True
            else:
                self._set_edge(j, a2, b2)
                self._set_edge(i, a1, b1)

    def edge_list(self):
        return [(self.ea[i], self.eb[i]) for i in range(len(self.ea))]


def _sa_growth(d, D, rng, deadline, s0, consider):
    """Grow a bipartite d-regular graph one vertex pair at a time, annealing at each size."""
    s = max(d + 2, s0)
    st = None
    while st is None:
        if time.monotonic() > deadline:
            return
        cand = _Bip()
        if cand.init_regular(s, d, rng):
            st = cand
        else:
            s += 1
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.05:
            break
        level_deadline = now + 0.5 * remaining
        if not st.anneal(D, rng, level_deadline, 3.0, 0.3):
            break
        consider(len(st.adj), st.edge_list())
        if not st.grow(d, rng):
            break


# ----------------------------------------------------------------------------
# Previous approach kept as a secondary family: bi-Cayley / group-voltage lifts
# over semidirect products Z_m x| Z_k2.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _groups_of_order(G, rng, cap=40):
    """All semidirect groups Z_m x| Z_k2 of order G (sampled up to `cap` r-values per k2)."""
    out = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            out.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:cap]:
            out.append((m, k2, r))
    return out


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _lift_cost(k, G, D, darts, perms):
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


def _lift_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _lift_trial(d, D, k, G, rng, iters, deadline, groups):
    if not groups:
        return None
    m, k2, r = rng.choice(groups)
    order, mul, _ = lib.semidirect_group(m, k2, r)
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = []
    for p in layers:
        for i in range(k):
            darts.append([i, p[i], rng.randrange(order)])
    perms = [_right_perm(mul, order, s) for _, _, s in darts]
    cost = _lift_cost(k, order, D, darts, perms)
    stall = 0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline or stall > 250:
            break
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_perm = perms[idx]
        new_s = rng.randrange(order)
        darts[idx][2] = new_s
        perms[idx] = _right_perm(mul, order, new_s)
        c2 = _lift_cost(k, order, D, darts, perms)
        if c2 < cost:
            stall = 0
        else:
            stall += 1
        if c2 <= cost or rng.random() < 0.02:
            cost = c2
        else:
            darts[idx][2] = old_s
            perms[idx] = old_perm

    if cost == 0:
        return _lift_edges(k, order, darts, perms)
    return None


def _lift_search(d, D, rng, deadline, holder, consider):
    group_cache = {}

    def groups_for(G):
        if G not in group_cache:
            group_cache[G] = _groups_of_order(G, rng)
        return group_cache[G]

    while time.monotonic() < deadline:
        best_n = holder[0]
        k = 1 if rng.random() < 0.75 else rng.choice([2, 3])
        base = best_n // (2 * k)
        span = max(3, base // 8)
        G = max(2, base + 1 + rng.randrange(0, span + 1))
        res = _lift_trial(d, D, k, G, rng, 800, deadline, groups_for(G))
        if res is not None:
            consider(res[0], res[1])


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = 0.8 * time_limit
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    holder = [best[0]]

    def consider(n, e):
        if n > holder[0] and lib.is_valid(n, e, d, D):
            nonlocal best
            best = (n, e)
            holder[0] = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    bold = d >= 4 and D >= 4
    if bold:
        # Short voltage-lift phase banks a solid graph first, then the
        # annealing growth search uses the rest of the budget.
        _lift_search(d, D, rng, start + 0.25 * budget, holder, consider)
        s0 = max(d + 2, holder[0] // 2 - 20)
        _sa_growth(d, D, rng, deadline, s0, consider)
    else:
        _lift_search(d, D, rng, deadline, holder, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
