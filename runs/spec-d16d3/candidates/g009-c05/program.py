import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction A (D = 3): arc-extended projective plane incidence graphs.
#
# Start from the incidence graph of PG(2, q). Each old vertex has spare degree
# s = d - q - 1. Add one new A-vertex per point P in S (joined to the q+1 lines
# through P) and one new B-vertex per line j in S (joined to the q+1 points on j).
# Pencil/line loads must stay within s, which is an arc-type condition on S.
# Order is 2(q^2+q+1) + 2|S|.
#
# Construction B (D = 3, new): local repair search. Starting from the best valid
# graph, add one A-vertex and one B-vertex, fill all spare degree greedily (added
# edges never increase distances), then run simulated annealing on degree-
# preserving edge swaps to drive the number of pairs at distance > 3 to zero.
# Repeat while time remains. Any result is re-checked by lib.is_valid.
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
    """Extended graph plus its bipartition flags (A = points and new A, B = lines and new B)."""
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
    isA = [True] * m + [False] * m + [True] * k + [False] * k
    return n, E, isA


def _arc_candidates(d, deadline, rng):
    """Return a list of (n, edges, isA) arc-extended graphs, one per usable prime power q."""
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
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Repair search (D = 3).
# ----------------------------------------------------------------------------

def _bad_pairs3(n, adj):
    """Number of unordered vertex pairs at distance > 3 (bitset balls of radius 3)."""
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        nxt = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt[v] = r
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


def _fill(n, adj, isA, d, rng, eset, tries=20000):
    """Greedily add random A-B edges between vertices with spare degree (never hurts diameter)."""
    da = [v for v in range(n) if isA[v] and len(adj[v]) < d]
    db = [v for v in range(n) if not isA[v] and len(adj[v]) < d]
    for _ in range(tries):
        if not da or not db:
            break
        i = rng.randrange(len(da))
        j = rng.randrange(len(db))
        a, b = da[i], db[j]
        if (a, b) in eset:
            continue
        eset.add((a, b))
        adj[a].append(b)
        adj[b].append(a)
        if len(adj[a]) >= d:
            da[i] = da[-1]
            da.pop()
        if len(adj[b]) >= d:
            db[j] = db[-1]
            db.pop()


def _remove_edge(adj, eset, a, b):
    adj[a].remove(b)
    adj[b].remove(a)
    eset.discard((a, b))


def _add_edge(adj, eset, a, b):
    adj[a].append(b)
    adj[b].append(a)
    eset.add((a, b))


def _anneal_repair(n, adj, isA, d, eset, deadline, rng):
    """Simulated annealing on degree-preserving edge swaps; returns (cost, edge list)."""
    A_list = [v for v in range(n) if isA[v]]
    B_list = [v for v in range(n) if not isA[v]]
    E = list(eset)
    cur = _bad_pairs3(n, adj)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now > deadline:
            break
        T = 1.5 * (1.0 - (now - t0) / span) + 0.05
        i = rng.randrange(len(E))
        a, b = E[i]
        a2 = rng.choice(A_list)
        b2 = rng.choice(B_list)
        if (a2, b2) == (a, b) or (a2, b2) in eset:
            continue
        if len(adj[a2]) - (a2 == a) >= d or len(adj[b2]) - (b2 == b) >= d:
            continue
        _remove_edge(adj, eset, a, b)
        _add_edge(adj, eset, a2, b2)
        new = _bad_pairs3(n, adj)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            E[i] = (a2, b2)
        else:
            _remove_edge(adj, eset, a2, b2)
            _add_edge(adj, eset, a, b)
    return cur, E


def _repair(n, edges, isA, d, deadline, rng):
    """Grow a valid D=3 graph by +2 vertices (one per side) while annealing succeeds."""
    cur_n, cur_edges, cur_isA = n, edges, isA
    moore3 = 2 * (1 + (d - 1) + (d - 1) ** 2)
    while time.monotonic() < deadline:
        nn = cur_n + 2
        if nn > moore3:
            break
        isA2 = cur_isA + [True, False]
        adj = [[] for _ in range(nn)]
        eset = set()
        for u, v in cur_edges:
            a, b = (u, v) if isA2[u] else (v, u)
            if (a, b) in eset:
                continue
            _add_edge(adj, eset, a, b)
        _fill(nn, adj, isA2, d, rng, eset)
        cost, E = _anneal_repair(nn, adj, isA2, d, eset, deadline, rng)
        if cost != 0:
            break
        cur_n, cur_edges, cur_isA = nn, E, isA2
    return cur_n, cur_edges, cur_isA


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4). Parent construction.
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
# Voltage lifts over semidirect products (D >= 2 fallback search). Parent construction.
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


def _anneal_voltage(d, D, k, G, mul, rng, deadline, iters):
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
# Entry point.
# ----------------------------------------------------------------------------

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
        # Stage 1: arc-extended projective plane graphs (parent construction).
        arc_deadline = start + 0.15 * time_limit
        cands = _arc_candidates(d, arc_deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        base = None
        for n_c, e_c, isA in cands:
            if lib.is_valid(n_c, e_c, d, D):
                base = (n_c, e_c, isA)
                break
        if base is not None:
            consider(base[0], base[1])
            # Stage 2: local repair search, growing from the arc graph.
            n_r, e_r, _ = _repair(base[0], base[1], base[2], d, deadline, rng)
            consider(n_r, e_r)
    else:
        # Other diameters: GQ baseline (D >= 4) and voltage-lift annealing (parent).
        if D >= 4 and time.monotonic() < deadline:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base_k = best_n // (2 * k)
            G = max(2, base_k + 1 + rng.randrange(0, max(3, base_k // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal_voltage(d, D, k, order, mul, rng, deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
