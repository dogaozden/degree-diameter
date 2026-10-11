import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane extensions (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with degree bound d it has spare
# s = d - q - 1.
#
# A-side: a family of "A-sets", each a set of R = d lines that covers every
#         point. Each family member becomes a new vertex adjacent to its lines.
#         Pairwise, two A-sets must share a line (so their new vertices are at
#         distance 2), and every line lies in at most s A-sets.
# B-side: the dual. Each B-set is a set of R = d points that meets every line,
#         pairwise sharing a point, with every point in at most s B-sets.
#
# Covering gives all old-to-new distances <= 3 automatically, and the A and B
# sides use disjoint degree budgets, so they are searched independently.
# The parent's conic families (pencils at conic points) are the starting point.
# The new search is simulated annealing that tries to add one more A-set (or
# B-set) at a time, keeping the last feasible family.
# Order = 2(q^2+q+1) + kA + kB.
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


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
    return out


def _family_search(s, R, tgt_of_el, el_of_tgt, init, rng, deadline):
    """Annealing search for the largest family of R-element sets.

    Elements are indexed 0..ne-1 and each element e covers the targets tgt_of_el[e].
    A feasible family has: every set covers all targets; every two sets share an
    element; every element lies in at most s sets. Starts from `init` (padded to R),
    and whenever a feasible family is reached one more random set is added.
    Returns the last feasible family as a list of lists, or None.
    """
    ne = len(tgt_of_el)
    nt = len(el_of_tgt)
    full = (1 << nt) - 1
    tmask = []
    for targets in tgt_of_el:
        mk = 0
        for t in targets:
            mk |= 1 << t
        tmask.append(mk)

    sets = [list(dict.fromkeys(b))[:R] for b in init]
    load = [0] * ne
    for S in sets:
        for e in S:
            load[e] += 1
    for S in sets:
        if len(S) < R:
            mem = set(S)
            cand = sorted((e for e in range(ne) if e not in mem),
                          key=lambda e: (load[e], rng.random()))
            for e in cand[:R - len(S)]:
                S.append(e)
                load[e] += 1

    def state():
        k = len(sets)
        mem = [set(S) for S in sets]
        emask, cov = [], []
        ld = [0] * ne
        for S in sets:
            em = 0
            cv = 0
            for e in S:
                em |= 1 << e
                cv |= tmask[e]
                ld[e] += 1
            emask.append(em)
            cov.append(cv)
        cost = sum(nt - c.bit_count() for c in cov)
        for i in range(k):
            for j in range(i + 1, k):
                if (emask[i] & emask[j]) == 0:
                    cost += 1
        cost += sum(max(0, x - s) for x in ld)
        return mem, emask, cov, ld, cost

    mem, emask, cov, load, cost = state()
    best = None
    T = 0.8
    it = 0
    while True:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        if cost == 0:
            best = [list(S) for S in sets]
            cand = sorted(range(ne), key=lambda e: (load[e], rng.random()))
            sets.append(cand[:R])
            mem, emask, cov, load, cost = state()
            T = 0.8
            continue

        k = len(sets)
        T = max(0.05, T * 0.9997)
        i = rng.randrange(k)
        S = sets[i]
        p = rng.randrange(R)
        e0 = S[p]
        r = rng.random()
        e1 = -1
        if r < 0.45:
            unc = full & ~cov[i]
            if unc:
                for _ in range(30):
                    t = rng.randrange(nt)
                    if (unc >> t) & 1:
                        lst = el_of_tgt[t]
                        e1 = lst[rng.randrange(len(lst))]
                        break
        elif r < 0.6:
            j = rng.randrange(k)
            if j != i and (emask[i] & emask[j]) == 0:
                e1 = sets[j][rng.randrange(R)]
        if e1 < 0:
            e1 = rng.randrange(ne)
        if e1 in mem[i]:
            continue

        newcov = 0
        for idx in range(R):
            e = e1 if idx == p else S[idx]
            newcov |= tmask[e]
        old_unc = nt - cov[i].bit_count()
        d_cost = (nt - newcov.bit_count()) - old_unc

        ei = emask[i]
        newem = ei ^ (1 << e0) ^ (1 << e1)
        for j in range(k):
            if j != i:
                ej = emask[j]
                if (ei & ej) == 0:
                    d_cost -= 1
                if (newem & ej) == 0:
                    d_cost += 1

        l0 = load[e0]
        l1 = load[e1]
        d_cost += max(0, l0 - 1 - s) - max(0, l0 - s)
        d_cost += max(0, l1 + 1 - s) - max(0, l1 - s)

        if d_cost <= 0 or rng.random() < math.exp(-d_cost / T):
            S[p] = e1
            mem[i].discard(e0)
            mem[i].add(e1)
            emask[i] = newem
            cov[i] = newcov
            load[e0] -= 1
            load[e1] += 1
            cost += d_cost
    return best


def _assemble(m, edges, famA, famB):
    """Build the graph: old PG incidence, one A-vertex per A-set, one B-vertex per B-set."""
    kA, kB = len(famA), len(famB)
    n = 2 * m + kA + kB
    E = list(edges)
    for a, X in enumerate(famA):
        x = 2 * m + a
        for L in X:
            E.append((x, m + L))
    for b, Y in enumerate(famB):
        y = 2 * m + kA + b
        for P in Y:
            E.append((P, y))
    return n, E


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

    # Arc-extended projective plane graphs (diameter 3, valid for all D >= 3).
    if D >= 3:
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    # Family search: grow the A-side and B-side families beyond the conic size.
    if D == 3:
        qs = [q for q in range(2, d) if lib.is_prime_power(q) and d - q - 1 >= 1]
        if qs:
            q = max(qs)
            s = d - q - 1
            m, edges, point_lines, line_points, index, pts = _pg_data(q)
            conic = _conic_set(q, index, lib.GF(q))
            famA = _family_search(s, d, line_points, point_lines,
                                  [point_lines[P] for P in conic],
                                  random.Random(seed * 31 + 1),
                                  start + 0.4 * time_limit)
            famB = _family_search(s, d, point_lines, line_points,
                                  [line_points[j] for j in conic],
                                  random.Random(seed * 31 + 2),
                                  start + 0.78 * time_limit)
            if famA and famB:
                consider(*_assemble(m, edges, famA, famB))

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
