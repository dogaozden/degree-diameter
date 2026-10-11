import itertools
import math
import random
import time

import lib


def _largest_prime_at_most(x):
    for p in range(x, 1, -1):
        if all(p % r for r in range(2, math.isqrt(p) + 1)):
            return p
    return None


def _gq_base(q):
    """Incidence graph of the generalized quadrangle W(q), q prime. Points 0..m-1, lines m..2m-1.
    Degree q+1, order 2(q+1)(q^2+1), diameter 4 (the Moore bound for d=q+1, D=4)."""
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    idx = {v: i for i, v in enumerate(pts)}
    m = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = pow(c, q - 2, q)
        return tuple((x * inv) % q for x in v)

    def form(x, y):
        return (x[0] * y[1] - x[1] * y[0] + x[2] * y[3] - x[3] * y[2]) % q

    lines = set()
    for i in range(m):
        P = pts[i]
        for j in range(i + 1, m):
            Q = pts[j]
            if form(P, Q):
                continue
            members = set()
            for a in range(q):
                for b in range(q):
                    if a or b:
                        v = tuple((a * P[k] + b * Q[k]) % q for k in range(4))
                        members.add(idx[norm(v)])
            lines.add(tuple(sorted(members)))
    lines = sorted(lines)
    if len(lines) != m:
        return None
    edges = [(p, m + j) for j, line in enumerate(lines) for p in line]
    return 2 * m, edges


def _bad(n, adj, D=4):
    """Number of unordered vertex pairs at distance > D (bitset ball expansion)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


class _State:
    """Bipartite graph with side-0 / side-1 vertices and degree cap; supports fill and edge rewiring."""

    def __init__(self, n, edges, cap, side, rng):
        self.n = n
        self.cap = cap
        self.side = list(side)
        self.rng = rng
        self.edges = [[a, b] for a, b in edges]
        self.adj = [set() for _ in range(n)]
        for a, b in self.edges:
            self.adj[a].add(b)
            self.adj[b].add(a)
        self._refresh_pools()

    def _refresh_pools(self):
        self.S0 = [v for v in range(self.n) if self.side[v] == 0]
        self.S1 = [v for v in range(self.n) if self.side[v] == 1]

    def snapshot(self):
        return (self.n, [(a, b) for a, b in self.edges], list(self.side))

    def add_pair(self):
        self.n += 2
        self.adj.append(set())
        self.adj.append(set())
        self.side.extend([0, 1])
        self._refresh_pools()

    def _link(self, a, b):
        self.adj[a].add(b)
        self.adj[b].add(a)
        self.edges.append([a, b])

    def fill(self):
        """Add edges between opposite-side vertices with spare capacity (monotone: never hurts)."""
        cap, adj = self.cap, self.adj
        A = [v for v in self.S0 if len(adj[v]) < cap]
        B = [v for v in self.S1 if len(adj[v]) < cap]
        self.rng.shuffle(A)
        self.rng.shuffle(B)
        for a in A:
            for b in B:
                if len(adj[a]) >= cap:
                    break
                if len(adj[b]) < cap and b not in adj[a]:
                    self._link(a, b)

    def _move(self, i, which, old, new):
        other = self.edges[i][1 - which]
        adj = self.adj
        adj[old].discard(other)
        adj[other].discard(old)
        adj[new].add(other)
        adj[other].add(new)
        self.edges[i][which] = new

    def rewire(self):
        """Move one endpoint of a random edge to another same-side vertex with spare capacity."""
        if not self.edges:
            return None
        rng, adj, cap = self.rng, self.adj, self.cap
        i = rng.randrange(len(self.edges))
        which = rng.randrange(2)
        other = self.edges[i][1 - which]
        old = self.edges[i][which]
        pool = self.S0 if which == 0 else self.S1
        for _ in range(30):
            c = pool[rng.randrange(len(pool))]
            if c != old and c not in adj[other] and len(adj[c]) < cap:
                self._move(i, which, old, c)
                return (i, which, old)
        return None

    def undo(self, i, which, old):
        cur = self.edges[i][which]
        self._move(i, which, cur, old)


def _anneal(st, deadline):
    """Simulated annealing on rewire moves, minimising bad pairs. Returns True if cost reaches 0."""
    rng = st.rng
    cur = _bad(st.n, st.adj)
    T = 1.0
    it = 0
    while cur > 0 and time.monotonic() < deadline:
        it += 1
        if it % 200 == 0:
            st.fill()
            cur = _bad(st.n, st.adj)
            if cur == 0:
                break
        mv = st.rewire()
        if mv is None:
            continue
        new = _bad(st.n, st.adj)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            st.undo(*mv)
        T = max(0.05, T * 0.9995)
    return cur == 0


def _grow(base, cap, seed, deadline):
    """Start from the GQ base (degree < cap, so spare capacity exists) and add vertex pairs
    (one point, one line) while annealing to diameter 4. Returns the largest valid graph found."""
    rng = random.Random(seed)
    n0, edges0 = base
    half = n0 // 2
    side0 = [0] * half + [1] * half
    best = (n0, list(edges0))
    st = _State(n0, edges0, cap, side0, rng)
    fails = 0
    while fails < 2 and time.monotonic() < deadline - 0.5:
        snap = st.snapshot()
        st.add_pair()
        st.fill()
        now = time.monotonic()
        attempt_end = min(deadline, now + max(3.0, 0.45 * (deadline - now)))
        if _anneal(st, attempt_end):
            best = (st.n, [(a, b) for a, b in st.edges])
            fails = 0
        else:
            fails += 1
            st = _State(snap[0], snap[1], cap, snap[2], rng)
    return best


def _parent_search(d, D, seed, deadline):
    """Fallback: Haar-graph search (valid for all cases)."""
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    best = None
    if D == 4:
        q = _largest_prime_at_most(d - 1)
        if q is not None and q >= 2:
            try:
                base = _gq_base(q)
            except Exception:
                base = None
            if base is not None and lib.is_valid(base[0], base[1], d, D):
                best = base
                try:
                    grown = _grow(base, d, seed, deadline)
                except Exception:
                    grown = None
                if (grown is not None and grown[0] > best[0]
                        and lib.is_valid(grown[0], grown[1], d, D)):
                    best = grown

    if best is None:
        best = _parent_search(d, D, seed, deadline)
    return best
