"""Bold variant: pure-Python bipartite voltage lifts over semidirect groups.

Instead of the C annealer over general lifts, this program searches bipartite voltage lifts
of small base graphs (1, 2 or 3 vertices per side) over metacyclic groups Z_m x|_r Z_k.
A lift with base degree d has vertices A_{i,x} and B_{j,y}, with x, y in the group. Dart (i, j, s)
joins A_{i,x} to B_{j,xs}. Left multiplication is an automorphism, so the diameter is <= D
iff a BFS of depth D from each of the 2*kb class representatives (A_{i,e} and B_{j,e}) reaches
everything. Each step needs only a few short BFS runs, so the search runs in pure Python.

Search: target vertex counts climb in steps of 2 from the current best. At each level,
random groups and dart sets are annealed on the number of unreached (representative, vertex)
pairs. A level that stalls for its time slice is skipped and the target rises, because
divisibility of the group order can make a larger target easier. Every result is checked
with lib.is_valid before it is accepted. Fallbacks are K_{d,d} and the known constructions
for D = 3 and D = 4, so every case returns a valid graph.
"""
import itertools
import math
import random
import time

import lib


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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


def known_start(d, D):
    """Best known construction Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
    return None


_GROUP_LIST_CACHE = {}


def _group_list(N):
    """All metacyclic groups Z_m x|_r Z_k of order N, as (m, k, r) triples."""
    if N in _GROUP_LIST_CACHE:
        return _GROUP_LIST_CACHE[N]
    out = []
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        if m == 1:
            out.append((1, k, 0))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    _GROUP_LIST_CACHE[N] = out
    return out


class _Group:
    """Z_m x|_r Z_k with element a*k+b, (a,b)(c,e) = (a + r^b c, b+e). Identity is index 0."""

    def __init__(self, m, k, r):
        self.m, self.k, self.N = m, k, m * k
        self.RP = [pow(r, b, m) for b in range(k)]
        self.rows = {}

    def mul(self, x, y):
        m, k = self.m, self.k
        a, b = divmod(x, k)
        c, e = divmod(y, k)
        return ((a + self.RP[b] * c) % m) * k + (b + e) % k

    def inv(self, x):
        m, k = self.m, self.k
        c, e = divmod(x, k)
        nb = (-e) % k
        a = (-self.RP[nb] * c) % m
        return a * k + nb

    def row(self, s):
        """row[x] = x * s, cached per s."""
        R = self.rows.get(s)
        if R is None:
            R = [self.mul(x, s) for x in range(self.N)]
            self.rows[s] = R
        return R


def _dup_free(darts):
    return len(set(darts)) == len(darts)


def _cost(G, kb, D, darts):
    """Number of unreached (representative, vertex) pairs; zero iff the lift has diameter <= D."""
    N = G.N
    V = 2 * kb * N
    nbr = [[] for _ in range(V)]
    for i, j, s in darts:
        R = G.row(s)
        base_b = kb * N + j * N
        for x in range(N):
            a = i * N + x
            b = base_b + R[x]
            nbr[a].append(b)
            nbr[b].append(a)
    total = 0
    for src in range(2 * kb):
        s0 = src * N
        seen = bytearray(V)
        seen[s0] = 1
        frontier = [s0]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in nbr[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += V - cnt
    return total


def _random_darts(G, kb, d, rng):
    darts = []
    for _ in range(d):
        perm = list(range(kb))
        rng.shuffle(perm)
        for i in range(kb):
            darts.append((i, perm[i], rng.randrange(G.N)))
    return darts


def _anneal(G, kb, d, D, steps, deadline, rng):
    """Anneal darts for one (group, kb). Returns darts with zero cost, or None."""
    darts = None
    for _ in range(20):
        cand = _random_darts(G, kb, d, rng)
        if _dup_free(cand):
            darts = cand
            break
    if darts is None:
        return None
    c = _cost(G, kb, D, darts)
    nd = len(darts)
    for step in range(steps):
        if c == 0:
            return darts
        if (step & 15) == 0 and time.monotonic() > deadline:
            return None
        T = 2.0 * (1.0 - step / steps) + 0.05
        new = list(darts)
        if kb < 2 or rng.random() < 0.6:
            t = rng.randrange(nd)
            i, j, s = new[t]
            s2 = rng.randrange(G.N)
            if s2 == s:
                continue
            new[t] = (i, j, s2)
        else:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(kb), 2)
            t1, t2 = l * kb + i1, l * kb + i2
            (a1, j1, s1), (a2, j2, s2) = new[t1], new[t2]
            new[t1] = (a1, j2, s1)
            new[t2] = (a2, j1, s2)
        if not _dup_free(new):
            continue
        c2 = _cost(G, kb, D, new)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            darts = new
            c = c2
    return darts if c == 0 else None


def _to_graph(G, kb, darts):
    N = G.N
    edges = []
    for i, j, s in darts:
        R = G.row(s)
        for x in range(N):
            edges.append((i * N + x, kb * N + j * N + R[x]))
    return 2 * kb * N, edges


def _search(d, D, best, deadline, rng):
    moore = lib.moore_bound(d, D)
    target = best[0] + 2
    while time.monotonic() < deadline and target <= moore:
        now = time.monotonic()
        level_end = min(deadline, now + max(2.0, 0.2 * (deadline - now)))
        success = False
        while time.monotonic() < level_end and not success:
            opts = [kb for kb in (1, 2, 3)
                    if target % (2 * kb) == 0 and (target // (2 * kb)) * kb >= d]
            if not opts:
                break
            kb = rng.choice(opts)
            N = target // (2 * kb)
            groups = _group_list(N)
            if not groups:
                break
            m, k, r = rng.choice(groups)
            G = _Group(m, k, r)
            steps = rng.randint(1500, 4000)
            darts = _anneal(G, kb, d, D, steps, level_end, rng)
            if darts is not None:
                n, edges = _to_graph(G, kb, darts)
                if n > best[0] and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    success = True
        target = best[0] + 2 if success else target + 2
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):
        return best

    deadline = t0 + 0.85 * time_limit - 1.0
    if deadline - time.monotonic() < 0.5:
        return best
    rng = random.Random(seed * 7919 + d * 131 + D)
    try:
        cand = _search(d, D, best, deadline, rng)
        if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    except Exception:
        pass
    return best
