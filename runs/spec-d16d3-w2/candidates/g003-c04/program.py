import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Absolute-flag extension search (D = 3).
#
# Base: incidence graph of PG(2, q), points 0..m-1, lines m..2m-1, with the
# standard polarity identifying point i with line i (incidence = dot product).
#
# New idea: a point a is "absolute" if a lies on the line with its own index,
# a . a = 0. Deleting the 2*(q+1) flags (a, line a) for absolute a leaves every
# absolute point and absolute line with one spare degree instead of none.
# Those spares, together with the usual spare degree d - (q+1) everywhere, host
# new vertices:
#   * an A-vertex for each s in SA, adjacent to the q+1 lines through s;
#   * a B-vertex for each t in SB, adjacent to the q+1 points on line t.
# Capacities are enforced exactly during search, so every state has max degree
# <= d and is bipartite. Diameter is checked by a penalty: bad pairs at distance
# > 3. The search maximises |SA| + |SB| - mu * bad, keeps the best state with
# zero bad pairs, and validates it with lib.is_valid.
#
# Counting: a non-absolute point can absorb at most 2 extra loads when d = q+3,
# an absolute one 3, so the sets can exceed the conic (size q+1) bound used by
# plain arc extensions.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _best_q(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _pg(q):
    """Return (m, pl, lp, absolute): pl[i] = lines through point i, lp[j] = points on line j."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        j = v - m
        pl[u].append(j)
        lp[j].append(u)
    absolute = [i for i in range(m) if i in pl[i]]
    return m, pl, lp, absolute


class _Ext:
    """Extension state: side 0 = new A-vertices (pencils), side 1 = new B-vertices (stars)."""

    def __init__(self, d, q, removed_flags):
        self.d = d
        self.m, self.pl, self.lp, self.absolute = _pg(q)
        m = self.m
        self.removed = set(self.absolute) if removed_flags else set()
        capP = [d - (len(self.pl[P]) - (P in self.removed)) for P in range(m)]
        capL = [d - (len(self.lp[j]) - (j in self.removed)) for j in range(m)]
        self.nbr = [self.pl, self.lp]
        self.cap = [capL, capP]
        self.reset()

    def reset(self):
        self.sets = [set(), set()]
        self.cnt = [[0] * self.m, [0] * self.m]

    def can_add(self, side, x):
        c, cap = self.cnt[side], self.cap[side]
        return all(c[y] < cap[y] for y in self.nbr[side][x])

    def add(self, side, x):
        self.sets[side].add(x)
        c = self.cnt[side]
        for y in self.nbr[side][x]:
            c[y] += 1

    def remove(self, side, x):
        self.sets[side].discard(x)
        c = self.cnt[side]
        for y in self.nbr[side][x]:
            c[y] -= 1

    def size(self):
        return len(self.sets[0]) + len(self.sets[1])

    def state(self):
        return sorted(self.sets[0]), sorted(self.sets[1])

    def load(self, SA, SB):
        self.reset()
        for s in SA:
            self.add(0, s)
        for t in SB:
            self.add(1, t)

    def seed_absolute(self):
        for s in self.absolute:
            for side in (0, 1):
                if s not in self.sets[side] and self.can_add(side, s):
                    self.add(side, s)

    def graph(self):
        m, pl, lp = self.m, self.pl, self.lp
        SA = sorted(self.sets[0])
        SB = sorted(self.sets[1])
        E = []
        for i in range(m):
            for j in pl[i]:
                if j == i and i in self.removed:
                    continue
                E.append((i, m + j))
        base = 2 * m
        for k, s in enumerate(SA):
            x = base + k
            for j in pl[s]:
                E.append((x, m + j))
        base += len(SA)
        for k, t in enumerate(SB):
            y = base + k
            for i in lp[t]:
                E.append((i, y))
        return base + len(SB), E

    def evaluate(self):
        n, E = self.graph()
        return lib.bad_pairs(n, E, 3), n, E


def _apply(ext, ops):
    """Apply ops ('add'|'rem', side, x) in order; return the done-list, or None if infeasible (state restored)."""
    done = []
    for act, side, x in ops:
        if act == 'add':
            ok = x not in ext.sets[side] and ext.can_add(side, x)
        else:
            ok = x in ext.sets[side]
        if not ok:
            _undo(ext, done)
            return None
        if act == 'add':
            ext.add(side, x)
        else:
            ext.remove(side, x)
        done.append((act, side, x))
    return done


def _undo(ext, done):
    for act, side, x in reversed(done):
        if act == 'add':
            ext.remove(side, x)
        else:
            ext.add(side, x)


def _search(ext, d, deadline, rng):
    """Annealing over (SA, SB) maximising size - mu*bad; returns best valid (n, edges) or None."""
    mu = 1.5
    bad, n, E = ext.evaluate()
    cur = bad - mu * ext.size()
    best = None
    best_size = -1
    best_state = None
    if bad == 0 and lib.is_valid(n, E, d, 3):
        best, best_size, best_state = (n, E), ext.size(), ext.state()
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    stale = 0
    while time.monotonic() < deadline:
        frac = min(1.0, (time.monotonic() - t0) / span)
        T = 1.5 * (1 - frac) + 0.15 * frac
        stale += 1
        if stale > 1500 and best_state is not None:
            ext.load(*best_state)
            bad, n, E = ext.evaluate()
            cur = bad - mu * ext.size()
            stale = 0
            continue
        r = rng.random()
        side = rng.randrange(2)
        if r < 0.4:
            ops = [('add', side, rng.randrange(ext.m))]
        else:
            if not ext.sets[side]:
                continue
            x = rng.choice(sorted(ext.sets[side]))
            if r < 0.6:
                ops = [('rem', side, x)]
            else:
                ops = [('rem', side, x), ('add', side, rng.randrange(ext.m))]
        done = _apply(ext, ops)
        if done is None:
            continue
        bad, n, E = ext.evaluate()
        new = bad - mu * ext.size()
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
            if bad == 0 and ext.size() > best_size and lib.is_valid(n, E, d, 3):
                best, best_size, best_state = (n, E), ext.size(), ext.state()
                stale = 0
        else:
            _undo(ext, done)
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (for D >= 4).
# ----------------------------------------------------------------------------

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


def _cost(k, G, D, darts, perms):
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


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
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
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        q = _best_q(d)
        if q is not None:
            # Plain incidence graph of PG(2, q): diameter 3, degree q + 1 <= d.
            base = _Ext(d, q, removed_flags=False)
            consider(*base.graph())

            # Parent-style conic arc: absolute points on both sides, no flag deletion.
            arc = _Ext(d, q, removed_flags=False)
            arc.seed_absolute()
            consider(*arc.graph())

            # New: absolute-flag removal with penalised extension search.
            ext = _Ext(d, q, removed_flags=True)
            ext.seed_absolute()
            res = _search(ext, d, deadline, rng)
            if res is not None:
                consider(res[0], res[1])
    elif D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base_sz = best_n // (2 * k)
            G = max(2, base_sz + 1 + rng.randrange(0, max(3, base_sz // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
