import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane extensions with "cover families" (diameter 3).
#
# Start from the incidence graph of PG(2, q): points 0..m-1, lines m..2m-1.
# Every old vertex has degree q+1, so spare s = d - q - 1.
#
# New point-side vertices X (joined only to lines) are described by a set T_X
# of lines with:
#   (a) every point lies on some line of T_X          (distance <= 2 to points)
#   (b) pairwise: T_X and T_Y share a line            (distance 2 between them)
#   (c) every line is in at most s sets T_X            (degree budget)
#   (d) |T_X| <= d                                     (degree of X)
# Line-side vertices are the point-dual: sets S_Y of points that meet every
# line, pairwise sharing a point, each point in at most s sets.
#
# Pencils (all lines through a point) are the classical members, which gives the
# arc construction (2(q^2+q+1) + 2*arc). General covers can be larger than a
# pencil, so the family search tries to add non-pencil members to the pencil
# family. Sides are independent, so the best A-family and B-family are combined.
# Every candidate is checked with lib.is_valid, and the plain PG graph and the
# pencil graph are always kept as fallbacks.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


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


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the load-constrained set problem."""
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _pencil_set(q, m, s, nbr, index, rng, deadline):
    """Load-feasible set of points (or lines) giving pencil members; conic used when larger."""
    S = _greedy_side(m, s, nbr, rng, 15, deadline)
    S = _local_search(m, s, nbr, S, rng, deadline, 15000)
    if s >= 2:
        cs = _conic_set(q, index, lib.GF(q))
        if len(cs) > len(S) and _loads_ok(cs, s, m, nbr):
            S = cs
    return S


def _cover_member(F, load, s, d, m, et, rng):
    """Try to add one new member to family F. Members are lists of elements.

    The new member shares an element with every existing member (using an
    element with load < s), then adds elements with load < s until every
    target is covered. On success the member is appended and loads are updated.
    """
    X = []
    inX = set()
    ok = True
    order = list(range(len(F)))
    rng.shuffle(order)
    for k in order:
        Y = F[k]
        if any(e in inX for e in Y):
            continue
        cands = [e for e in Y if load[e] < s]
        if not cands:
            ok = False
            break
        e = rng.choice(cands)
        inX.add(e)
        X.append(e)
        load[e] += 1
    if ok:
        covered = [False] * m
        for e in X:
            for t in et[e]:
                covered[t] = True
        nun = covered.count(False)
        while nun > 0 and len(X) < d:
            best_e, best_v = -1, -1.0
            for e in range(m):
                if e in inX or load[e] >= s:
                    continue
                c = 0
                for t in et[e]:
                    if not covered[t]:
                        c += 1
                if c == 0:
                    continue
                v = c + 0.5 * rng.random()
                if v > best_v:
                    best_e, best_v = e, v
            if best_e < 0:
                break
            inX.add(best_e)
            X.append(best_e)
            load[best_e] += 1
            for t in et[best_e]:
                if not covered[t]:
                    covered[t] = True
                    nun -= 1
        ok = nun == 0 and len(X) <= d
    if ok:
        F.append(X)
        return True
    for e in X:
        load[e] -= 1
    return False


def _remove_member(F, load, k):
    """Remove member k from the family, releasing its loads."""
    for e in F[k]:
        load[e] -= 1
    F.pop(k)


def _family(m, s, d, et, init, rng, deadline):
    """Local search over cover families, starting from init. Returns the best family found."""
    F = [list(X) for X in init]
    load = [0] * m
    for X in F:
        for e in X:
            load[e] += 1
    if any(x > s for x in load):
        return []
    best = [list(X) for X in F]
    best_size = len(F)
    while time.monotonic() < deadline:
        if _cover_member(F, load, s, d, m, et, rng):
            if len(F) > best_size:
                best = [list(X) for X in F]
                best_size = len(F)
            continue
        if not F:
            break
        saved = [list(X) for X in F]
        saved_load = list(load)
        old = len(F)
        _remove_member(F, load, rng.randrange(len(F)))
        for _ in range(3):
            _cover_member(F, load, s, d, m, et, rng)
        if len(F) < old:
            F[:] = saved
            load[:] = saved_load
    return best


def _family_graph(m, edges, FA, FB):
    """Build the graph: PG(2,q) incidence plus one vertex per A-member and per B-member."""
    n = 2 * m + len(FA) + len(FB)
    E = list(edges)
    for t, X in enumerate(FA):
        x = 2 * m + t
        for L in X:
            E.append((x, m + L))
    base = 2 * m + len(FA)
    for t, Y in enumerate(FB):
        y = base + t
        for P in Y:
            E.append((P, y))
    return n, E


def _projective_phase(d, rng, deadline, consider):
    """Run the family search on the most promising prime powers q with q + 1 <= d."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * (s * mm // (q + 1))

    qs.sort(key=lambda q: -bound(q))
    qs = qs[:2]
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now >= deadline:
            break
        frac = 0.6 if (idx == 0 and len(qs) > 1) else 1.0
        dl = now + (deadline - now) * frac
        sl = dl - now
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        consider(2 * m, list(edges))
        s = d - q - 1
        if s < 1:
            continue
        SA = _pencil_set(q, m, s, point_lines, index, rng, now + 0.05 * sl)
        SB = _pencil_set(q, m, s, line_points, index, rng, now + 0.10 * sl)
        initA = [list(point_lines[P]) for P in SA]
        initB = [list(line_points[j]) for j in SB]
        consider(*_family_graph(m, edges, initA, initB))
        t_b = now + 0.10 * sl
        a_end = t_b + 0.45 * (dl - t_b)
        # A-members are sets of lines covering points; B-members are sets of points covering lines.
        FA = _family(m, s, d, line_points, initA, rng, a_end)
        FB = _family(m, s, d, point_lines, initB, rng, dl)
        consider(*_family_graph(m, edges, FA, FB))


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
# Simulated annealing over bi-Cayley voltage lifts (for D >= 4).
# ----------------------------------------------------------------------------

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

    # Diameter-3 constructions: PG(2,q) plus cover families on the spare degree.
    if D >= 3:
        proj_end = start + (0.8 if D == 3 else 0.35) * time_limit
        _projective_phase(d, rng, proj_end, consider)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

        end = start + 0.85 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, end, iters=400)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
