import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane extensions for diameter 3, with a new "family packing" search.
#
# Base: incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1), degree q+1.
# Spare degree per old vertex is s = d - q - 1.
#
# New X-vertices (point side) each carry a set N of lines. New Y-vertices carry
# a set M of points. For diameter 3 the full set of conditions reduces to:
#   X-side: every point lies on a line of N (covering), and any two new
#           X-neighbourhoods share a line (pairwise intersection);
#   Y-side: symmetric (every line contains a point of M, and any two M's meet);
#   loads: each line is in <= s sets N, each point is in <= s sets M, and every
#          set has size <= d.
# X and Y are independent, so each side is a separate packing problem.
#
# New idea in this version: instead of only choosing single pencils (the parent's
# arc extension), each side is a "family" of arbitrary covering sets, and we search
# for one more set than the current family by simulated annealing over element
# insertions and removals. Cost = uncovered targets + non-intersecting pairs +
# capacity overflow + size overflow. Cost 0 gives an exactly valid family, and the
# final graph is still checked with lib.is_valid.
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


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target is hit by <= s chosen elements."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_side(m, s, nbr, S0, rng, deadline, iters=6000):
    """Plateau local search for a set with each target hit <= s times; returns the largest set seen."""
    if s < 1:
        return list(S0)
    inS = [False] * m
    load = [0] * m
    S = list(S0)
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            load[t] += 1
    best = list(S)
    for it in range(iters):
        if it % 256 == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        over = {t for t in nbr[x] if load[t] >= s}
        if not over:
            S.append(x)
            inS[x] = True
            for t in nbr[x]:
                load[t] += 1
            if len(S) > len(best):
                best = list(S)
            continue
        cand = [y for y in S if any(t in over for t in nbr[y])]
        if not cand:
            continue
        y = rng.choice(cand)
        for t in nbr[y]:
            load[t] -= 1
        if all(load[t] < s for t in nbr[x]):
            S.remove(y)
            inS[y] = False
            S.append(x)
            inS[x] = True
            for t in nbr[x]:
                load[t] += 1
        else:
            for t in nbr[y]:
                load[t] += 1
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


# ----------------------------------------------------------------------------
# Family packing: sets of elements covering targets, pairwise intersecting,
# with element load <= s and set size <= d. Simulated annealing with incremental cost.
# ----------------------------------------------------------------------------

class _Family:
    """Incremental state for k sets over elements 0..m-1 covering targets 0..m-1."""

    def __init__(self, m, s, d, cover, tgt, k):
        self.m, self.s, self.d = m, s, d
        self.cover = cover          # element -> list of targets it covers
        self.tgt = tgt              # target -> list of elements covering it
        self.k = k
        self.S = [set() for _ in range(k)]
        self.cov = [[0] * m for _ in range(k)]
        self.holders = [set() for _ in range(m)]
        self.load = [0] * m
        self.inter = [[0] * k for _ in range(k)]
        self.U = k * m              # uncovered (set, target) pairs
        self.I = k * (k - 1) // 2   # pairs of sets with empty intersection
        self.O = 0                  # total load overflow
        self.Z = 0                  # sets over size d

    def cost(self):
        return self.U + self.I + self.O + self.Z

    def add(self, i, e):
        S = self.S[i]
        S.add(e)
        ci = self.cov[i]
        for t in self.cover[e]:
            if ci[t] == 0:
                self.U -= 1
            ci[t] += 1
        ii = self.inter[i]
        h = self.holders[e]
        for j in h:
            if ii[j] == 0:
                self.I -= 1
            ii[j] += 1
            self.inter[j][i] += 1
        h.add(i)
        if self.load[e] >= self.s:
            self.O += 1
        self.load[e] += 1
        if len(S) > self.d:
            self.Z += 1

    def remove(self, i, e):
        S = self.S[i]
        if len(S) > self.d:
            self.Z -= 1
        S.discard(e)
        ci = self.cov[i]
        for t in self.cover[e]:
            ci[t] -= 1
            if ci[t] == 0:
                self.U += 1
        h = self.holders[e]
        h.discard(i)
        ii = self.inter[i]
        for j in h:
            ii[j] -= 1
            self.inter[j][i] -= 1
            if ii[j] == 0:
                self.I += 1
        if self.load[e] > self.s:
            self.O -= 1
        self.load[e] -= 1


def _rand_out(S, m, rng):
    """Random element of range(m) not in S."""
    while True:
        e = rng.randrange(m)
        if e not in S:
            return e


def _propose(fam, rng):
    """Apply one random move to fam and return the list of ops (kind 1 = add, 0 = remove)."""
    m = fam.m
    i = rng.randrange(fam.k)
    S = fam.S[i]
    ops = []
    r = rng.random()
    if r < 0.45:
        ci = fam.cov[i]
        unc = [t for t in range(m) if ci[t] == 0]
        if unc:
            t = rng.choice(unc)
            e = rng.choice(fam.tgt[t])
            if e not in S:
                if len(S) >= fam.d and S:
                    x = rng.choice(tuple(S))
                    fam.remove(i, x)
                    ops.append((0, i, x))
                fam.add(i, e)
                ops.append((1, i, e))
                return ops
    if r < 0.7:
        if len(S) < m:
            e = _rand_out(S, m, rng)
            fam.add(i, e)
            ops.append((1, i, e))
    elif r < 0.85:
        if S:
            x = rng.choice(tuple(S))
            fam.remove(i, x)
            ops.append((0, i, x))
    else:
        if S:
            x = rng.choice(tuple(S))
            fam.remove(i, x)
            ops.append((0, i, x))
            e = _rand_out(S, m, rng)
            fam.add(i, e)
            ops.append((1, i, e))
    return ops


def _solve_family(m, s, d, cover, tgt, init, rng, deadline):
    """Anneal from the k = len(init) sets in `init`. Return a valid family (lists) or None."""
    fam = _Family(m, s, d, cover, tgt, len(init))
    for i, S in enumerate(init):
        for e in S:
            fam.add(i, e)
    cur = fam.cost()
    T0, T1 = 1.2, 0.05
    T = T0
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    it = 0
    while cur > 0:
        it += 1
        if it % 64 == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        ops = _propose(fam, rng)
        new = fam.cost()
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            for kind, i, e in reversed(ops):
                if kind:
                    fam.remove(i, e)
                else:
                    fam.add(i, e)
    if cur == 0:
        return [sorted(S) for S in fam.S]
    return None


def _grow_both(m, s, d, pl, lp, Xs, Ys, rng, deadline):
    """Try to enlarge each side's family by one set at a time, alternating sides."""
    sides = {
        # X-side: elements are lines, targets are points.
        "X": {"sets": Xs, "cover": lp, "tgt": pl,
              "fresh": lambda: list(pl[rng.randrange(m)]), "fails": 0},
        # Y-side: elements are points, targets are lines.
        "Y": {"sets": Ys, "cover": pl, "tgt": lp,
              "fresh": lambda: list(lp[rng.randrange(m)]), "fails": 0},
    }
    active = ["X", "Y"]
    while active:
        for key in list(active):
            now = time.monotonic()
            rem = deadline - now
            if rem <= 0.05:
                return sides["X"]["sets"], sides["Y"]["sets"]
            c = sides[key]
            end = min(deadline, now + max(0.5, rem / 3.0))
            init = [list(x) for x in c["sets"]] + [c["fresh"]()]
            res = _solve_family(m, s, d, c["cover"], c["tgt"], init, rng, end)
            if res is None:
                c["fails"] += 1
                if c["fails"] >= 3:
                    active.remove(key)
            else:
                c["sets"] = res
                c["fails"] = 0
    return sides["X"]["sets"], sides["Y"]["sets"]


def _graph(m, edges, Xs, Ys):
    """PG(2,q) incidence plus one vertex per X-set (joined to lines) and per Y-set (joined to points)."""
    nx = len(Xs)
    n = 2 * m + nx + len(Ys)
    E = list(edges)
    for t, S in enumerate(Xs):
        x = 2 * m + t
        E.extend((x, m + L) for L in S)
    for t, S in enumerate(Ys):
        y = 2 * m + nx + t
        E.extend((P, y) for P in S)
    return n, E


def _seed_sets(q, d, rng, deadline):
    """Seed point/line sets from greedy, conic and local search (as in the arc extension)."""
    m, edges, pl, lp, index, pts = _pg_data(q)
    s = d - q - 1
    SA = _greedy_side(m, s, pl, rng, 40, deadline)
    SB = _greedy_side(m, s, lp, rng, 40, deadline)
    if s >= 2:
        cs = _conic_set(q, index, lib.GF(q))
        if len(cs) > len(SA) and _loads_ok(cs, s, m, pl):
            SA = cs
        if len(cs) > len(SB) and _loads_ok(cs, s, m, lp):
            SB = cs
    SA = _local_side(m, s, pl, SA, rng, deadline)
    SB = _local_side(m, s, lp, SB, rng, deadline)
    return m, edges, pl, lp, SA, SB


def _projective_search(d, deadline, rng):
    """Candidate graphs from the largest prime-power planes with q + 1 <= d."""
    out = []
    qs = [q for q in range(min(d - 1, 23), 1, -1) if lib.is_prime_power(q)]
    for idx, q in enumerate(qs[:2]):
        now = time.monotonic()
        if now >= deadline:
            break
        s = d - q - 1
        if s == 0:
            out.append(lib.projective_plane_incidence(q))
            break
        share = deadline - now
        sub_deadline = now + (0.8 * share if idx == 0 else share)
        m, edges, pl, lp, SA, SB = _seed_sets(q, d, rng, now + 0.2 * share)
        Xs = [list(pl[P]) for P in SA]
        Ys = [list(lp[L]) for L in SB]
        out.append(_graph(m, edges, Xs, Ys))
        Xs, Ys = _grow_both(m, s, d, pl, lp, Xs, Ys, rng, sub_deadline)
        out.append(_graph(m, edges, Xs, Ys))
    return out


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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
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


def _cost(k, G, D, darts, perms):
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


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
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
    deadline = start + max(0.5, 0.8 * time_limit)
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

    # Projective-plane extensions with family packing (diameter 3, valid for D >= 3).
    if D >= 3:
        for n_c, e_c in _projective_search(d, deadline, rng):
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Group voltage lifts for D >= 4 (the D = 3 search already used the time budget).
    if D >= 4:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
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
