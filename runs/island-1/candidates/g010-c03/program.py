import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _largest_pp_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _araujo_candidate(d):
    """Araujo-Pardo-Lopez graph for the largest prime power q <= d - 2 (degree q + 2 <= d)."""
    q = _largest_pp_le(d - 2)
    if q is None or q < 3:
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except Exception:
        return None


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
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


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
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


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Growth: slack filling and cover-based vertex extension (diameter-preserving).
# ----------------------------------------------------------------------------

def _fill_slack(n, edges, d, seed):
    """Greedily add edges between opposite-colour vertices with spare degree."""
    adjs = [set() for _ in range(n)]
    for u, v in edges:
        adjs[u].add(v)
        adjs[v].add(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adjs[u]:
                if color[w] == -1:
                    color[w] = 1 - color[u]
                    stack.append(w)
    deg = [len(a) for a in adjs]
    rng = random.Random(seed)
    out = list(edges)
    for _ in range(4):
        A = [v for v in range(n) if color[v] == 0 and deg[v] < d]
        B = [v for v in range(n) if color[v] == 1 and deg[v] < d]
        rng.shuffle(A)
        rng.shuffle(B)
        added = False
        for a in A:
            for b in B:
                if deg[a] >= d:
                    break
                if deg[b] < d and b not in adjs[a]:
                    adjs[a].add(b)
                    adjs[b].add(a)
                    deg[a] += 1
                    deg[b] += 1
                    out.append((a, b))
                    added = True
        if not added:
            break
    return n, out


def _greedy_cover(cands, reach, full, d, rng):
    """Pick up to d candidates whose balls cover full; return list or None."""
    pool = list(cands)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while len(chosen) < d and covered != full:
        best = None
        best_gain = 0
        for c in pool:
            g = (reach[c] & ~covered).bit_count()
            if g > best_gain:
                best, best_gain = c, g
        if best is None:
            break
        chosen.append(best)
        covered |= reach[best]
        pool = [c for c in pool if c != best]
    if covered == full:
        return chosen
    return None


def _extend(n, edges, d, D, seed, deadline):
    """Attach new vertices to spare-degree vertices while keeping diameter <= D and bipartiteness."""
    if D < 2 or n == 0:
        return n, list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    if any(len(a) > d for a in adj):
        return n, list(edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if color[w] == -1:
                    color[w] = 1 - color[u]
                    stack.append(w)
                elif color[w] == color[u]:
                    return n, list(edges)
    rng = random.Random(seed)
    out = list(edges)
    R = D - 1
    fails = 0
    while fails < 4 and time.monotonic() < deadline:
        N = len(adj)
        full = (1 << N) - 1
        reach = [1 << v for v in range(N)]
        for _ in range(R):
            nxt = []
            for v in range(N):
                r = reach[v]
                for u in adj[v]:
                    r |= reach[u]
                nxt.append(r)
            reach = nxt
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for opp in sides:
            cands = [c for c in range(N) if color[c] == opp and len(adj[c]) < d]
            if not cands:
                continue
            chosen = _greedy_cover(cands, reach, full, d, rng)
            if chosen:
                x = N
                adj.append(set(chosen))
                color.append(1 - opp)
                for c in chosen:
                    adj[c].add(x)
                    out.append((c, x))
                added = True
                break
        if added:
            fails = 0
        else:
            fails += 1
    return len(adj), out


def _grow(n, edges, d, D, seed, deadline):
    """Fill slack, extend by cover vertices, then fill slack again."""
    n, e = _fill_slack(n, edges, d, seed)
    n, e = _extend(n, e, d, D, seed, deadline)
    return _fill_slack(n, e, d, seed + 1)


# ----------------------------------------------------------------------------
# Group-voltage lifts over semidirect products Z_m x| Z_k2, annealed.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# Each layer is a permutation i -> p[i], so every vertex has degree d.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(lo, hi, rng):
    """Return (order, mul) for a random semidirect product of a random order G in [lo, hi], or None."""
    for _ in range(40):
        G = rng.randrange(lo, hi + 1)
        divs = [k2 for k2 in range(1, 17) if G % k2 == 0 and G // k2 >= 2]
        if not divs:
            continue
        k2 = rng.choice(divs)
        m = G // k2
        cands = [1]  # r = 1 gives the abelian group Z_m x Z_k2
        if k2 > 1:
            cands += [r for r in rng.sample(range(2, m), min(m - 2, 120))
                      if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
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


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid.

    If the running total exceeds `limit`, returns early with a value above `limit`.
    """
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
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Metropolis annealing over voltages and per-layer B-assignments.

    A move with new cost c2 is accepted iff c2 <= cost - T*ln(u), u ~ Uniform(0, 1].
    That threshold doubles as the early-exit limit for the cost evaluation.
    """
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = []
    for p in layers:
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.05 ** (it / iters))
        u = 1.0 - rng.random()
        limit = cost - T * math.log(u)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def _search(d, D, k, lo, hi, rng, iters, deadline):
    """Sample a group of order in [lo, hi] and anneal voltages on it. Returns (n, edges) or None."""
    g = _sample_group(lo, hi, rng)
    if g is None:
        return None
    G, mul = g
    return _anneal(d, D, k, G, mul, rng, deadline, iters)


# ----------------------------------------------------------------------------
# Haar graph hill-climb (small D, secondary family).
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    span = deadline - start
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    moore = lib._moore_bound(d, D)

    # Base constructions.
    bases = []
    arcs = []
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            bases.append(pg)
        al = _araujo_candidate(d)
        if al is not None:
            bases.append(al)
        arcs = _arc_extensions(d, start + 0.2 * span, random.Random(seed * 7919 + d))
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            bases.append(gq)

    for b in bases:
        consider(b[0], b[1])
    for c in arcs:
        consider(c[0], c[1])
    if arcs:
        bases.append(max(arcs, key=lambda c: c[0]))

    # Grow each base by spare-degree vertices, within a bounded share of the budget.
    grow_end = start + 0.35 * span
    for idx, (n0, e0) in enumerate(bases):
        if best_n >= moore:
            break
        now = time.monotonic()
        if now >= grow_end:
            break
        slice_end = now + (grow_end - now) / (len(bases) - idx)
        n1, e1 = _grow(n0, e0, d, D, seed + idx, slice_end)
        consider(n1, e1)

    # Main search: annealed voltage lifts over semidirect products, with an
    # occasional Haar attempt for small D.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    haar_m, haar_miss = d + 1, 0
    while time.monotonic() < deadline and best_n < moore:
        if D <= 4 and haar_miss < 4 and rng.random() < 0.1:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
            continue

        k = rng.choice(ks)
        lo = max(2, best_n // (2 * k) + 1)
        hi = int(lo * 1.35) + 2
        res = _search(d, D, k, lo, hi, rng, 1500, deadline)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
