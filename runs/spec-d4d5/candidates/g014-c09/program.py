import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Direct search on the bipartite graph itself.
#
# Idea: keep one concrete bipartite graph (sides 0 and 1, every edge joins them)
# and grow it one vertex at a time. Each growth step attaches a new vertex with
# "steal-attach": a full opposite-side vertex gives up one edge to the newcomer,
# and the displaced same-side vertex becomes spare. Then simulated annealing
# repairs distances using degree-preserving edge switches (a1-b1, a2-b2 ->
# a1-b2, a2-b1), spare-slot additions and occasional removals. The cost is the
# number of vertex pairs at distance > D, computed with bitmask balls. The
# search only accepts states with zero cost, so every recorded graph is valid.
# ----------------------------------------------------------------------------


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (bitmask balls)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


class _State:
    """Bipartite graph with fixed sides, an edge list with positions, and adjacency sets."""

    def __init__(self, n, side, edges, d):
        self.n = n
        self.side = list(side)
        self.d = d
        self.adj = [set() for _ in range(n)]
        self.E = []
        self.pos = {}
        for p, q in edges:
            self.add_edge(p, q)

    def _orient(self, p, q):
        return (p, q) if self.side[p] == 0 else (q, p)

    def add_edge(self, p, q):
        a, b = self._orient(p, q)
        self.pos[(a, b)] = len(self.E)
        self.E.append((a, b))
        self.adj[a].add(b)
        self.adj[b].add(a)

    def remove_edge(self, p, q):
        a, b = self._orient(p, q)
        i = self.pos.pop((a, b))
        last = self.E.pop()
        if i < len(self.E):
            self.E[i] = last
            self.pos[last] = i
        self.adj[a].discard(b)
        self.adj[b].discard(a)

    def add_vertex(self, s):
        self.side.append(s)
        self.adj.append(set())
        self.n += 1
        return self.n - 1


def _snap(st):
    return (st.n, list(st.side), list(st.E))


def _restore(snap, d):
    n, side, E = snap
    return _State(n, side, E, d)


def _spare(st, s):
    return [v for v in range(st.n) if st.side[v] == s and len(st.adj[v]) < st.d]


def _try_add(st, rng):
    sa = _spare(st, 0)
    sb = _spare(st, 1)
    if not sa or not sb:
        return None
    for _ in range(12):
        a = rng.choice(sa)
        b = rng.choice(sb)
        if b not in st.adj[a]:
            return [('+', a, b)]
    return None


def _try_switch(st, rng):
    m = len(st.E)
    if m < 2:
        return None
    a1, b1 = st.E[rng.randrange(m)]
    a2, b2 = st.E[rng.randrange(m)]
    if a1 == a2 or b1 == b2 or b2 in st.adj[a1] or b1 in st.adj[a2]:
        return None
    return [('-', a1, b1), ('-', a2, b2), ('+', a1, b2), ('+', a2, b1)]


def _apply(st, ops):
    for k, a, b in ops:
        if k == '+':
            st.add_edge(a, b)
        else:
            st.remove_edge(a, b)


def _undo(st, ops):
    for k, a, b in reversed(ops):
        if k == '+':
            st.remove_edge(a, b)
        else:
            st.add_edge(a, b)


def _anneal(st, D, rng, deadline, iters):
    """Metropolis search on the cost (bad pairs). Returns True when the cost reaches 0."""
    cost = _bad(st.n, st.adj, D)
    if cost == 0:
        return True
    T0 = max(0.5, 0.05 * cost)
    T1 = 0.2
    decay = (T1 / T0) ** (1.0 / max(1, iters))
    T = T0
    for it in range(iters):
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = max(T1, T * decay)
        r = rng.random()
        if r < 0.2:
            ops = _try_add(st, rng)
        elif r < 0.23:
            if not st.E:
                continue
            a, b = st.E[rng.randrange(len(st.E))]
            ops = [('-', a, b)]
        else:
            ops = _try_switch(st, rng)
        if ops is None:
            continue
        _apply(st, ops)
        c2 = _bad(st.n, st.adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost == 0:
                return True
        else:
            _undo(st, ops)
    return cost == 0


def _saturate(st, rng):
    """Add edges between spare opposite-side vertices. This never increases distances."""
    sa = _spare(st, 0)
    sb = _spare(st, 1)
    pairs = [(a, b) for a in sa for b in sb if b not in st.adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(st.adj[a]) < st.d and len(st.adj[b]) < st.d and b not in st.adj[a]:
            st.add_edge(a, b)


def _grow(st, rng):
    """Steal-attach a new vertex: each slot takes a spare opposite vertex, or displaces an edge."""
    d = st.d
    s = rng.randrange(2)
    x = st.add_vertex(s)
    for _ in range(d):
        opp = [v for v in range(st.n)
               if st.side[v] == 1 - s and v != x and v not in st.adj[x] and len(st.adj[v]) < d]
        if opp:
            st.add_edge(x, rng.choice(opp))
            continue
        full = [v for v in range(st.n)
                if st.side[v] == 1 - s and v != x and v not in st.adj[x]]
        if not full:
            break
        u = rng.choice(full)
        cand = list(st.adj[u])
        if not cand:
            break
        w = rng.choice(cand)
        st.remove_edge(w, u)
        st.add_edge(x, u)


def _base(d, D):
    """Projective plane incidence when d-1 is a prime power and D >= 3; else K_{d,d}."""
    if D >= 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        side = [0] * (n // 2) + [1] * (n // 2)
        return n, e, side
    n, e = lib.haar_graph(d, range(d))
    side = [0] * d + [1] * d
    return n, e, side


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 1.0)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))
    n0, e0, side0 = _base(d, D)
    if not lib.is_valid(n0, e0, d, D):
        return fallback

    rng = random.Random(seed)
    best_n, best_e = n0, list(e0)
    st = _State(n0, side0, e0, d)
    snap = _snap(st)

    while time.monotonic() < deadline:
        ok = False
        for k in range(1, 5):
            if _anneal(st, D, rng, deadline, 300 * k):
                ok = True
                break
            if time.monotonic() >= deadline:
                break
        if not ok:
            st = _restore(snap, d)
            continue
        _saturate(st, rng)
        if st.n > best_n and lib.is_valid(st.n, st.E, d, D):
            best_n, best_e = st.n, list(st.E)
        snap = _snap(st)
        _grow(st, rng)

    best = (best_n, best_e)
    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
