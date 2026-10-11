import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane base and arc seeds (diameter 3).
#
# PG(2, q) incidence: points 0..m-1, lines m..2m-1. Every vertex has degree q+1,
# so spare capacity s = d - q - 1 per vertex.
#
# Two families of new vertices are attached:
#   A-vertices: each joined to a set T of lines (block family). Valid when T
#               covers every point (each point lies on a line of T), any two
#               A-sets share a line, and every line is used by <= s sets.
#   B-vertices: dual, each joined to a set U of points covering every line,
#               pairwise sharing a point, every point used by <= s sets.
# Distances: A-A and B-B are 2 via the shared line/point; A to point is 2; A to
# line is 3; A to B is 3 (a line of T through a point of U). So diameter 3 holds.
#
# Seeds are pencils (T = lines through a point P, U = points on a line), which
# is the classic arc extension. New sets are grown by simulated annealing on a
# generic cover-family state (see _Family / _anneal).
# ----------------------------------------------------------------------------


def _pg(q):
    """Return (m, point_lines, line_points) for PG(2, q); lines use the same indices as points."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, point_lines, line_points


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines of S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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


def _setup(q, d, rng, seed_deadline):
    """Seed arc S (pencil centres / dual lines) for PG(2,q) under spare capacity s = d-q-1."""
    s = d - q - 1
    m, point_lines, line_points = _pg(q)
    S = _greedy_arc(m, s, point_lines, line_points, rng, 25, seed_deadline) if s >= 1 else []
    if s >= 2:
        F = lib.GF(q)
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        cs = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
        if q % 2 == 0:
            cs.append(index[(0, 1, 0)])
        if len(cs) > len(S) and _loads_ok(cs, s, m, point_lines, line_points):
            S = cs
    if S and not _loads_ok(S, s, m, point_lines, line_points):
        S = []
    return {
        "q": q, "s": s, "m": m, "pl": point_lines, "lp": line_points,
        "S": S, "order": 2 * m + 2 * len(S),
    }


# ----------------------------------------------------------------------------
# Generic cover-family state.
#
# Universe: U elements. Blocks: nb indices. be[b] = elements covered by block b.
# eb[e] = blocks covering element e. A family is a list of sets of blocks.
# Cost = (uncovered elements summed over sets)
#      + (number of set pairs sharing no block)
#      + (overflow: sum over blocks of max(0, #sets using block - s)).
# Cost 0 means: each set covers U, sets pairwise intersect, loads <= s,
# and each set has <= cap blocks.
# ----------------------------------------------------------------------------

class _Family:
    def __init__(self, U, nb, be, eb, cap, s, sets):
        self.U = U
        self.be = be
        self.eb = eb
        self.cap = cap
        self.s = s
        k = len(sets)
        self.members = [set() for _ in range(k)]
        self.cnt = [[0] * U for _ in range(k)]
        self.uncov = [U] * k
        self.shared = [[0] * k for _ in range(k)]
        self.holders = [[] for _ in range(nb)]
        self.cost = k * U + k * (k - 1) // 2
        for i, blocks in enumerate(sets):
            for b in blocks:
                if b not in self.members[i]:
                    self._add(i, b)

    def _add(self, i, b):
        self.members[i].add(b)
        cnt = self.cnt[i]
        for e in self.be[b]:
            if cnt[e] == 0:
                self.uncov[i] -= 1
                self.cost -= 1
            cnt[e] += 1
        h = self.holders[b]
        if len(h) >= self.s:
            self.cost += 1
        for j in h:
            if self.shared[i][j] == 0:
                self.cost -= 1
            self.shared[i][j] += 1
            self.shared[j][i] += 1
        h.append(i)

    def _remove(self, i, b):
        self.members[i].discard(b)
        cnt = self.cnt[i]
        for e in self.be[b]:
            cnt[e] -= 1
            if cnt[e] == 0:
                self.uncov[i] += 1
                self.cost += 1
        h = self.holders[b]
        h.remove(i)
        if len(h) >= self.s:
            self.cost -= 1
        for j in h:
            self.shared[i][j] -= 1
            self.shared[j][i] -= 1
            if self.shared[i][j] == 0:
                self.cost += 1

    def export(self):
        return [sorted(x) for x in self.members]


def _anneal(F, rng, deadline, iters):
    """Simulated annealing over the family; True if cost reaches 0."""
    k = len(F.members)
    if k == 0:
        return True
    U = F.U
    T0 = 0.8
    for it in range(iters):
        if F.cost == 0:
            return True
        if (it & 511) == 0 and time.monotonic() > deadline:
            return False
        T = T0 * (1.0 - it / iters) + 0.02
        i = rng.randrange(k)
        mem = F.members[i]
        cnt = F.cnt[i]
        r = rng.random()
        e = None
        if F.uncov[i] > 0:
            for _ in range(40):
                x = rng.randrange(U)
                if cnt[x] == 0:
                    e = x
                    break
        if r < 0.45 and len(mem) < F.cap:
            if e is None:
                e = rng.randrange(U)
            cands = F.eb[e]
            b = cands[rng.randrange(len(cands))]
            if b in mem:
                continue
            old = F.cost
            F._add(i, b)
            if F.cost > old and rng.random() >= math.exp(-(F.cost - old) / T):
                F._remove(i, b)
        elif r < 0.7 and len(mem) > 1:
            b = rng.choice(tuple(mem))
            old = F.cost
            F._remove(i, b)
            if F.cost > old and rng.random() >= math.exp(-(F.cost - old) / T):
                F._add(i, b)
        else:
            if not mem:
                continue
            if e is None:
                e = rng.randrange(U)
            cands = F.eb[e]
            bn = cands[rng.randrange(len(cands))]
            if bn in mem:
                continue
            bo = rng.choice(tuple(mem))
            old = F.cost
            F._remove(i, bo)
            F._add(i, bn)
            if F.cost > old and rng.random() >= math.exp(-(F.cost - old) / T):
                F._remove(i, bn)
                F._add(i, bo)
    return F.cost == 0


def _grow(U, nb, be, eb, cap, s, sets, rng, deadline, iters):
    """Repeatedly try to add one more valid set (seeded by a random cover) and anneal."""
    sets = [list(x) for x in sets]
    fails = 0
    while fails < 3 and time.monotonic() < deadline:
        e = rng.randrange(U)
        cand = sets + [list(eb[e])]
        F = _Family(U, nb, be, eb, cap, s, cand)
        if _anneal(F, rng, deadline, iters):
            sets = F.export()
            fails = 0
        else:
            fails += 1
    return sets


def _assemble(m, pl, A, B):
    """Base PG incidence plus A-vertices (line sets) and B-vertices (point sets)."""
    na = len(A)
    nb = len(B)
    E = []
    for P in range(m):
        for L in pl[P]:
            E.append((P, m + L))
    base = 2 * m
    for i, Ls in enumerate(A):
        x = base + i
        for L in Ls:
            E.append((x, m + L))
    base2 = base + na
    for j, Ps in enumerate(B):
        y = base2 + j
        for P in Ps:
            E.append((P, y))
    return base2 + nb, E


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.6 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D < 3:
        return best

    # Choose the projective plane order whose seed graph is largest.
    seeds = []
    seed_deadline = t0 + 0.2 * time_limit
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q) or q + 1 > d:
            continue
        seeds.append(_setup(q, d, rng, seed_deadline))
    if not seeds:
        return best

    st = max(seeds, key=lambda t: t["order"])
    m, pl, lp, s, S = st["m"], st["pl"], st["lp"], st["s"], st["S"]

    # Seed families: pencils through S for A, dual pencils for B.
    A = [list(pl[P]) for P in S]
    B = [list(lp[P]) for P in S]
    n0, E0 = _assemble(m, pl, A, B)
    if lib.is_valid(n0, E0, d, D) and n0 > best[0]:
        best = (n0, E0)

    # Grow both families with annealing on the remaining time (only if spare capacity exists).
    if s >= 1 and time.monotonic() < deadline:
        now = time.monotonic()
        mid = now + 0.5 * (deadline - now)
        # A-family: universe = points, blocks = lines, be = lines->points, eb = points->lines.
        A = _grow(m, m, lp, pl, d, s, A, rng, mid, 30000)
        # B-family: universe = lines, blocks = points, be = points->lines, eb = lines->points.
        B = _grow(m, m, pl, lp, d, s, B, rng, deadline, 30000)
        n1, E1 = _assemble(m, pl, A, B)
        if n1 > best[0] and lib.is_valid(n1, E1, d, D):
            best = (n1, E1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
