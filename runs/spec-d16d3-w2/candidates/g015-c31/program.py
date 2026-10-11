import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Asymmetric arc extensions of PG(2, q) (diameter 3).
#
# Start from the point-line incidence graph of PG(2, q). Every old vertex has
# degree q+1. Choose
#   C: a set of points, each line containing at most s of them;
#   T: a set of lines, each point lying on at most s of them, s = d - q - 1.
# For P in C add an "A-vertex" joined to the q+1 lines through P (a pencil).
# For j in T add a "B-vertex" joined to the q+1 points on j (a dual pencil).
# The two choices are independent: the parent forced C = T. Distances still
# work out: A-A share the line PP', B-B share the point j n j', an A-vertex
# reaches every old point in 2 steps (pencil), every old line in 3 (via the
# meet point), and an A-vertex to a B-vertex in 3 (via the line through P and
# the meet point of that line with j).
#
# Search: (1,2)-swap local search with randomized greedy restarts, plus the
# conic (k=q+1 for odd q, q+2 for even q) as a seed.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); lines are indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _loads_ok(chosen, s, n_cont, inc):
    """True if every container is hit by at most s chosen items."""
    load = [0] * n_cont
    for i in chosen:
        for c in inc[i]:
            load[c] += 1
            if load[c] > s:
                return False
    return True


def _greedy_bounded(inc, n_cont, s, rng, trials, deadline):
    """Randomized greedy: add items while every container stays at load <= s."""
    best = []
    order = list(range(len(inc)))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * n_cont
        chosen = []
        for i in order:
            ci = inc[i]
            if all(load[c] < s for c in ci):
                chosen.append(i)
                for c in ci:
                    load[c] += 1
        if len(chosen) > len(best):
            best = chosen
    return best


def _improve(chosen, inc, n_cont, s, rng, deadline):
    """(1,2)-swap local search: drop one item if at least two items can replace it."""
    cur = set(chosen)
    N = len(inc)
    while time.monotonic() < deadline:
        load = [0] * n_cont
        for i in cur:
            for c in inc[i]:
                load[c] += 1
        improved = False
        order = list(cur)
        rng.shuffle(order)
        for i in order:
            if time.monotonic() >= deadline:
                break
            for c in inc[i]:
                load[c] -= 1
            cand = [j for j in range(N) if j not in cur and all(load[c] < s for c in inc[j])]
            rng.shuffle(cand)
            added = []
            for j in cand:
                if all(load[c] < s for c in inc[j]):
                    added.append(j)
                    for c in inc[j]:
                        load[c] += 1
            if len(added) >= 2:
                cur.discard(i)
                cur.update(added)
                improved = True
                break
            for j in added:
                for c in inc[j]:
                    load[c] -= 1
            for c in inc[i]:
                load[c] += 1
        if not improved:
            break
    return sorted(cur)


def _maximize(inc, n_cont, s, rng, deadline, seeds):
    """Largest bounded-load set found from the given seeds plus restarts until deadline."""
    if s <= 0 or not inc:
        return []
    best = []
    for sd in seeds:
        if _loads_ok(sd, s, n_cont, inc):
            cand = _improve(list(sd), inc, n_cont, s, rng, deadline)
            if len(cand) > len(best):
                best = cand
    while time.monotonic() < deadline:
        g = _greedy_bounded(inc, n_cont, s, rng, 1, deadline)
        g = _improve(g, inc, n_cont, s, rng, deadline)
        if len(g) > len(best):
            best = g
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _assemble(m, edges, pl, lp, C, T):
    """Old PG incidence plus one A-vertex per point of C and one B-vertex per line of T."""
    n = 2 * m + len(C) + len(T)
    E = list(edges)
    x = 2 * m
    for P in C:
        for L in pl[P]:
            E.append((x, m + L))
        x += 1
    for j in T:
        for Q in lp[j]:
            E.append((Q, x))
        x += 1
    return n, E


def _arc_for_q(q, d, deadline, rng):
    """Best asymmetric arc extension of PG(2, q) for degree d, or None."""
    s = d - q - 1
    if s < 0:
        return None
    m, edges, pl, lp = _pg_data(q)
    seeds = []
    if s >= 2:
        F = lib.GF(q)
        index = {p: i for i, p in enumerate(lib.projective_points(q))}
        seeds.append(_conic_set(q, index, F))
    now = time.monotonic()
    mid = now + (deadline - now) / 2
    C = _maximize(pl, m, s, rng, mid, seeds)
    T = _maximize(lp, m, s, rng, deadline, seeds)
    return _assemble(m, edges, pl, lp, C, T)


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
# Simulated annealing over bi-Cayley voltage lifts.
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


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
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

    # Asymmetric arc extensions: diameter 3, so valid for all D >= 3.
    if D >= 3:
        arc_deadline = start + (0.6 if D == 3 else 0.3) * time_limit
        qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]
        for idx, q in enumerate(qs):
            now = time.monotonic()
            if now > arc_deadline:
                break
            share = (arc_deadline - now) / (len(qs) - idx)
            res = _arc_for_q(q, d, now + share, random.Random(seed * 7919 + q))
            if res is not None:
                consider(res[0], res[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts for the remaining time. For D >= 5 use larger bases.
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
