import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane base (diameter 3).
#
# Points are 0..m-1, lines are m..2m-1 (lib.projective_plane_incidence).
# New "A" vertices sit on the point side and are joined to a set of lines
# (a cover). New "B" vertices sit on the line side and are joined to a set of
# points (a cover). Degree and diameter hold exactly when, per side:
#   (1) every cover hits every point (for A) or every line (for B),
#   (2) any two covers on the same side share an element,
#   (3) every element lies in at most s = d - q - 1 covers (its spare degree).
# The two sides are independent, so each is searched on its own.
# ----------------------------------------------------------------------------

def _choose_q(d):
    """Largest prime power q with q + 1 <= d and spare degree d - q - 1 >= 1, else the largest q."""
    qs = [q for q in range(2, d) if lib.is_prime_power(q)]
    if not qs:
        return None
    spare = [q for q in qs if d - q - 1 >= 1]
    return max(spare) if spare else max(qs)


def _pg_structure(q):
    """Return (m, edges, pl, lp): pl[point] = lines through it, lp[line] = points on it."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _conic_indices(q):
    """Conic (plus nucleus for even q): an arc with at most two points on any line."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _conic_ok(S, s, m, pl, lp):
    """True if S gives valid loads: <= s points of S per line and <= s lines of S per point."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
    for L in S:
        for Q in lp[L]:
            cp[Q] += 1
    return max(cl) <= s and max(cp) <= s


# ----------------------------------------------------------------------------
# Cover-family search (new routine).
#
# A family is a list of covers (lists of elements). State keeps incremental
# counters so one swap (replace element a by b in cover i) is cheap.
# cost = uncovered (cover, universe item) pairs
#      + non-intersecting cover pairs
#      + load overflow beyond s.
# Simulated annealing with focused moves: pick an uncovered universe item and
# bring in an element that covers it.
# Growth: start from the conic-pencil family (valid), add a random cover, and
# anneal until cost 0 again; repeat until the deadline.
# ----------------------------------------------------------------------------

class _Family:
    def __init__(self, U, E, inc, univ, s, covers):
        self.U = U
        self.E = E
        self.inc = inc        # element -> universe items it covers
        self.univ = univ      # universe item -> elements covering it
        self.s = s
        self.covers = [list(c) for c in covers]
        k = self.k = len(self.covers)
        self.mem = [[False] * E for _ in range(k)]
        self.cov = [[0] * U for _ in range(k)]
        self.load = [0] * E
        for i, c in enumerate(self.covers):
            for e in c:
                self.mem[i][e] = True
                self.load[e] += 1
                for u in inc[e]:
                    self.cov[i][u] += 1
        self.total_uncov = sum(row.count(0) for row in self.cov)
        self.inter = [[0] * k for _ in range(k)]
        for i in range(k):
            for j in range(i + 1, k):
                x = sum(1 for e in self.covers[i] if self.mem[j][e])
                self.inter[i][j] = x
                self.inter[j][i] = x
        self.zero_pairs = sum(1 for i in range(k) for j in range(i + 1, k)
                              if self.inter[i][j] == 0)
        self.over = sum(max(0, x - s) for x in self.load)

    def cost(self):
        return self.total_uncov + self.zero_pairs + self.over

    def swap(self, i, a, b):
        """Replace element a by element b in cover i (b must not be in cover i)."""
        cov = self.cov[i]
        for u in self.inc[a]:
            cov[u] -= 1
            if cov[u] == 0:
                self.total_uncov += 1
        for u in self.inc[b]:
            if cov[u] == 0:
                self.total_uncov -= 1
            cov[u] += 1
        mem = self.mem
        row = self.inter[i]
        for j in range(self.k):
            if j == i:
                continue
            da = 1 if mem[j][a] else 0
            db = 1 if mem[j][b] else 0
            if da != db:
                old = row[j]
                new = old - da + db
                if old == 0 and new != 0:
                    self.zero_pairs -= 1
                elif old != 0 and new == 0:
                    self.zero_pairs += 1
                row[j] = new
                self.inter[j][i] = new
        la = self.load[a]
        if la > self.s:
            self.over -= 1
        self.load[a] = la - 1
        lb = self.load[b]
        if lb >= self.s:
            self.over += 1
        self.load[b] = lb + 1
        mem[i][a] = False
        mem[i][b] = True
        c = self.covers[i]
        c[c.index(a)] = b


def _cover_anneal(fam, deadline, rng, T, iters):
    """Simulated annealing on a _Family. Returns the final cost (0 means a valid family)."""
    cost = fam.cost()
    U, E = fam.U, fam.E
    for it in range(iters):
        if cost == 0:
            break
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(fam.k)
        ci = fam.covers[i]
        a = ci[rng.randrange(len(ci))]
        b = -1
        if rng.random() < 0.7:
            cov_i = fam.cov[i]
            for _ in range(6):
                u = rng.randrange(U)
                if cov_i[u] == 0:
                    opts = fam.univ[u]
                    b = opts[rng.randrange(len(opts))]
                    break
        if b < 0:
            b = rng.randrange(E)
        if fam.mem[i][b]:
            continue
        fam.swap(i, a, b)
        new = fam.cost()
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
        else:
            fam.swap(i, b, a)
    return cost


def _grow_family(U, E, inc, univ, s, size, init, deadline, rng):
    """Largest valid cover family found: start from init, add random covers, re-anneal."""
    covers = [list(c) for c in init]
    best = []
    while True:
        fam = _Family(U, E, inc, univ, s, covers)
        cost = fam.cost()
        while cost > 0 and time.monotonic() < deadline:
            cost = _cover_anneal(fam, deadline, rng, 0.5, 20000)
        if cost > 0:
            break
        best = [list(c) for c in fam.covers]
        if time.monotonic() >= deadline:
            break
        covers = best + [rng.sample(range(E), min(size, E))]
    return best


def _assemble(m, base_edges, covA, covB):
    """Base incidence graph plus A-vertices (point side, joined to lines) and B-vertices (line side, joined to points)."""
    kA, kB = len(covA), len(covB)
    n = 2 * m + kA + kB
    E = list(base_edges)
    for i, cov in enumerate(covA):
        x = 2 * m + i
        E.extend((x, m + L) for L in cov)
    for j, cov in enumerate(covB):
        y = 2 * m + kA + j
        E.extend((P, y) for P in cov)
    return n, E


def _pg_route(d, rng, start, time_limit, consider):
    q = _choose_q(d)
    if q is None:
        return
    m, edges, pl, lp = _pg_structure(q)
    consider(2 * m, edges)
    s = d - q - 1
    if s < 1:
        return
    size = min(d, m)
    S = _conic_indices(q)
    if _conic_ok(S, s, m, pl, lp):
        initA = [list(pl[P]) for P in S]   # pencils at conic points
        initB = [list(lp[L]) for L in S]   # dual pencils on conic lines
    else:
        initA, initB = [], []
    # Side A: elements are lines, universe is points.
    covA = _grow_family(m, m, lp, pl, s, size, initA, start + 0.42 * time_limit, rng)
    # Side B: elements are points, universe is lines.
    covB = _grow_family(m, m, pl, lp, s, size, initB, start + 0.80 * time_limit, rng)
    n, E = _assemble(m, edges, covA, covB)
    consider(n, E)


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products (used for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
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
    return [mul(g, s) for g in range(G)]


def _lift_cost(k, G, D, darts, perms):
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


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
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
            c2 = _lift_cost(k, G, D, darts, perms)
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
            c2 = _lift_cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _lift_edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d}: bipartite, degree d, diameter 2. Optimal for D = 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback
    box = [fallback]

    def consider(n, e):
        if n > box[0][0] and lib.is_valid(n, e, d, D):
            box[0] = (n, e)

    if D == 3:
        _pg_route(d, rng, start, time_limit, consider)
    else:
        deadline = start + 0.8 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = box[0][0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal_lift(d, D, k, order, mul, rng, deadline, 400)
            if res is not None:
                consider(res[0], res[1])

    n, e = box[0]
    if not lib.is_valid(n, e, d, D):
        return fallback
    return n, e
