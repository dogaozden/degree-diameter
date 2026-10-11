import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a multiset SA of points (repeats allowed). Each entry P gets a new
#         vertex joined to all q+1 lines through P. Constraint: every line
#         holds <= s entries of SA.
# B-side: a multiset SB of lines. Each entry j gets a new vertex joined to all
#         q+1 points on j. Constraint: every point lies on <= s entries of SB.
#
# Diameter stays 3 for any multisets SA, SB (see the derivation in the notes).
#
# New in this version: the multiset selection is solved by a simulated
# annealing packing search (_pack). Each move inserts a random candidate and
# ejects the few entries that block it, so it can escape the plateau that the
# greedy fill gets stuck on. Only the prime powers q whose upper bound
# 2m + 2*floor(s*m/(q+1)) can beat the best greedy order are searched.
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
    """True if every target t is hit by <= s entries of S (repeats counted), where entry x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy(m, s, nbr, rng):
    """One randomised greedy fill: add candidates while all their targets stay within load s.

    Loads only grow, so a candidate rejected once stays rejected; one pass is enough.
    """
    order = list(range(m))
    rng.shuffle(order)
    load = [0] * m
    S = []
    for x in order:
        nb = nbr[x]
        while all(load[t] < s for t in nb):
            S.append(x)
            for t in nb:
                load[t] += 1
    return S


def _put(ent, hit, nbr, e, x):
    """Insert entry id e with candidate x, updating the per-target hit sets."""
    ent[e] = x
    for t in nbr[x]:
        hit[t].add(e)


def _drop(ent, hit, nbr, e):
    """Remove entry id e, updating the hit sets; return its candidate."""
    x = ent.pop(e)
    for t in nbr[x]:
        hit[t].discard(e)
    return x


def _pack(m, s, nbr, rng, deadline, init):
    """Simulated annealing for a multiset packing with load cap s.

    Objective: number of entries, subject to every target t being hit by at most s entries.
    Move: pick a random candidate y. If it is feasible, insert it. Otherwise eject entries
    from its blocked targets (at most 3), then insert y if the result is feasible.
    The change is accepted with Metropolis probability exp(delta / T), where delta is the
    change in size, and the temperature cools geometrically to the deadline.
    Returns the largest feasible multiset seen.
    """
    if s < 1:
        return []
    ent = {}
    hit = [set() for _ in range(m)]
    nid = 0
    for x in init:
        if all(len(hit[t]) < s for t in nbr[x]):
            _put(ent, hit, nbr, nid, x)
            nid += 1
    best = list(ent.values())

    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T0, T1 = 0.6, 0.08
    T = T0
    it = 0
    exp = math.exp
    while True:
        it += 1
        if not (it & 127):
            now = time.monotonic()
            if now >= deadline:
                break
            T = T0 * (T1 / T0) ** ((now - start) / span)

        y = rng.randrange(m)
        ny = nbr[y]
        blocked = [t for t in ny if len(hit[t]) >= s]
        if not blocked:
            _put(ent, hit, nbr, nid, y)
            nid += 1
            if len(ent) > len(best):
                best = list(ent.values())
            continue

        removed = []
        for t in blocked:
            while len(hit[t]) >= s:
                if len(removed) >= 3:
                    break
                e = rng.choice(sorted(hit[t]))
                removed.append((e, _drop(ent, hit, nbr, e)))
            if len(hit[t]) >= s:
                break

        feasible = all(len(hit[t]) < s for t in ny)
        delta = 1 - len(removed)
        if feasible and (delta >= 0 or rng.random() < exp(delta / T)):
            _put(ent, hit, nbr, nid, y)
            nid += 1
            if len(ent) > len(best):
                best = list(ent.values())
        else:
            for e, x in reversed(removed):
                _put(ent, hit, nbr, e, x)
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA entry and one new B-vertex per SB entry."""
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
    """Return a list of (n, edges) candidates from arc-extended PG(2,q) graphs, for prime powers q with q + 1 <= d."""
    qs = [q for q in range(2, min(d - 1, 23) + 1)
          if lib.is_prime_power(q) and d - q - 1 >= 1]

    # Quick greedy pass for every q: gives a floor that a q must beat to be searched.
    pre = []
    for q in qs:
        s = d - q - 1
        m, edges, pl, lp, index, _ = _pg_data(q)
        F = lib.GF(q)
        SA = _greedy(m, s, pl, rng)
        SB = _greedy(m, s, lp, rng)
        if s >= 2:
            cs = _conic_set(q, index, F)
            if len(cs) > len(SA) and _loads_ok(cs, s, m, pl):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, lp):
                SB = cs
        n_init = 2 * m + len(SA) + len(SB)
        pre.append({"q": q, "s": s, "m": m, "edges": edges, "pl": pl, "lp": lp,
                    "SA": SA, "SB": SB, "n": n_init})

    out = []
    for item in pre:
        if _loads_ok(item["SA"], item["s"], item["m"], item["pl"]) and \
           _loads_ok(item["SB"], item["s"], item["m"], item["lp"]):
            out.append(_arc_graph(item["m"], item["edges"], item["pl"], item["lp"],
                                  item["SA"], item["SB"]))

    floor = max((item["n"] for item in pre), default=0)
    # Upper bound for q: 2m + 2*floor(s*m/(q+1)) (each entry uses q+1 line/point slots of capacity s*m).
    todo = []
    for item in pre:
        m, s, q = item["m"], item["s"], item["q"]
        ub = 2 * m + 2 * ((s * m) // (q + 1))
        if ub > floor:
            todo.append((ub, item))
    todo.sort(key=lambda t: -t[0])

    for idx, (ub, item) in enumerate(todo):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(todo) - idx)
        q, s, m = item["q"], item["s"], item["m"]
        pl, lp = item["pl"], item["lp"]
        t0 = time.monotonic()
        SA = _pack(m, s, pl, rng, t0 + share / 2, item["SA"])
        SB = _pack(m, s, lp, rng, t0 + share, item["SB"])
        if _loads_ok(SA, s, m, pl) and _loads_ok(SB, s, m, lp):
            out.append(_arc_graph(m, item["edges"], pl, lp, SA, SB))
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
# Simulated annealing over bi-Cayley voltage lifts.
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
    arc_deadline = start + 0.72 * time_limit
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

    # Arc-extended projective plane graphs with annealed A and B multisets.
    # Diameter 3, so valid for all D >= 3.
    if D >= 3:
        cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
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
