import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Multiset-extended projective plane graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q): points 0..m-1, lines m..2m-1,
# every old vertex of degree q+1. With d >= q+1 each old vertex has spare
# capacity s = d - q - 1.
#
# Add a multiset T of "point-type" vertices x_P (P a point, adjacent to all
# q+1 lines through P) and a multiset U of "line-type" vertices y_j (j a line,
# adjacent to all q+1 points on j). Capacity needs:
#   every line L:  #{copies P in T with P on L} <= s
#   every point Q: #{copies j in U with Q on j} <= s
# The two conditions are independent, so T and U are chosen by the same packing
# search (the dual problem is the same problem with points and lines swapped).
#
# Diameter stays 3: x_P reaches every point within 2 (through a line PQ), every
# line within 3 (through a line through P), and every y_j within 3 (through a
# line L through P meeting j). Symmetric for y_j. Two copies of the same
# type share a neighbour. The graph is bipartite with sides
# {points} + {x_P} and {lines} + {y_j}.
#
# Order = 2(q^2+q+1) + |T| + |U|. The old arc construction (0/1 multiplicities
# on a conic) gives |T|=|U|=q+1; multisets allow up to about q*s per side
# (for d=16, q=13, s=2: up to 26 per side, giving 418 instead of 394).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); points 0..m-1, lines are indices 0..m-1 too."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _pack(N, cons_of, items_of, cap, rng, deadline, T0=0.9, T1=0.08):
    """Maximise the total multiplicity of items 0..N-1 subject to load[c] <= cap for every constraint c.

    Item x adds one unit to each constraint in cons_of[x]; items_of[c] lists the items on constraint c.
    Simulated annealing with addition moves that evict conflicting units, plus removal moves.
    Returns the best multiplicity list found.
    """
    C = len(items_of)
    load = [0] * C
    mult = [0] * N
    total = 0
    best_total = 0
    best = mult[:]
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T = T0
    it = 0
    while True:
        it += 1
        if (it & 63) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = (now - start) / span
            T = T0 * (T1 / T0) ** frac

        x = rng.randrange(N)
        if mult[x] > 0 and rng.random() < 0.1:
            # Removal move.
            if rng.random() < math.exp(-1.0 / T):
                mult[x] -= 1
                for c in cons_of[x]:
                    load[c] -= 1
                total -= 1
            continue

        # Addition move: evict units from overloaded constraints of x.
        log = []
        ok = True
        for c in cons_of[x]:
            while load[c] >= cap:
                cand = [y for y in items_of[c] if y != x and mult[y] > 0]
                if not cand:
                    ok = False
                    break
                y = rng.choice(cand)
                mult[y] -= 1
                for c2 in cons_of[y]:
                    load[c2] -= 1
                log.append(y)
            if not ok:
                break
        if not ok:
            for y in reversed(log):
                mult[y] += 1
                for c2 in cons_of[y]:
                    load[c2] += 1
            continue

        delta = 1 - len(log)
        if delta >= 0 or rng.random() < math.exp(delta / T):
            mult[x] += 1
            for c in cons_of[x]:
                load[c] += 1
            total += delta
            if total > best_total:
                best_total = total
                best = mult[:]
        else:
            for y in reversed(log):
                mult[y] += 1
                for c2 in cons_of[y]:
                    load[c2] += 1
    return best


def _extended_graph(m, edges, point_lines, line_points, T_mult, U_mult):
    """Build PG(2,q) incidence plus x-vertices (per point copy) and y-vertices (per line copy)."""
    E = list(edges)
    n = 2 * m
    for P, k in enumerate(T_mult):
        for _ in range(k):
            x = n
            n += 1
            for L in point_lines[P]:
                E.append((x, m + L))
    for j, k in enumerate(U_mult):
        for _ in range(k):
            y = n
            n += 1
            for Q in line_points[j]:
                E.append((Q, y))
    return n, E


def _extension_candidates(d, best_n, deadline, rng):
    """Return a list of (n, edges) candidates from multiset-extended PG(2, q) for prime powers q with q+1 <= d."""
    todo = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        m = q * q + q + 1
        ub = 2 * m + 2 * (m * s) // (q + 1)  # fractional upper bound on the order
        if ub > best_n:
            todo.append((q, s))

    out = []
    for idx, (q, s) in enumerate(todo):
        now = time.monotonic()
        if now >= deadline:
            break
        budget_end = now + (deadline - now) / (len(todo) - idx)
        m, edges, point_lines, line_points = _pg_data(q)
        if s == 0:
            out.append((2 * m, list(edges)))
            continue
        half = now + (budget_end - now) / 2
        T_mult = _pack(m, point_lines, line_points, s, rng, half)
        U_mult = _pack(m, line_points, point_lines, s, rng, budget_end)
        out.append(_extended_graph(m, edges, point_lines, line_points, T_mult, U_mult))
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
# Simulated annealing over bi-Cayley voltage lifts (unchanged from parent).
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
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
    ext_deadline = start + 0.5 * time_limit
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

    # Multiset-extended projective plane graphs. Diameter 3, so valid for all D >= 3.
    if D >= 3:
        cands = _extension_candidates(d, best_n, ext_deadline,
                                      random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: annealed group voltage lifts. For D >= 5 use larger bases.
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
