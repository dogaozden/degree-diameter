import math
import random
import time
import itertools

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q): points 0..m-1 (side 0), lines
# m..2m-1 (side 1). Spare degree s = d - q - 1 on every old vertex allows:
#   * a set SA of points: each gets a new side-0 vertex joined to the q+1 lines
#     through it (each line may carry at most s such points);
#   * a set SB of lines: each gets a new side-1 vertex joined to the q+1 points
#     on it (each point may lie on at most s such lines).
# SA and SB are chosen independently (arcs and dual arcs).
#
# New change: after this construction, a generic growth phase tries to add
# further vertices. A new vertex X on side s is joined to a set N of vertices
# on the other side with spare degree, chosen by greedy set cover so that every
# side-s vertex is within distance 2 of N. X is kept only if a BFS from X
# reaches every vertex within D. Adding X never lengthens existing paths, so the
# graph stays valid.
# ----------------------------------------------------------------------------


def _pg(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, res_of):
    """True if no resource is used by more than s items of S."""
    cnt = [0] * m
    for i in S:
        for r in res_of[i]:
            cnt[r] += 1
    return max(cnt, default=0) <= s


def _pack(m, s, res_of, rng, trials, deadline):
    """Randomized greedy: largest found S with every resource used at most s times."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cnt = [0] * m
        S = []
        for i in order:
            if all(cnt[r] < s for r in res_of[i]):
                S.append(i)
                for r in res_of[i]:
                    cnt[r] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _assemble(m, edges, point_lines, line_points, SA, SB):
    """Adjacency sets and side labels of the extended graph."""
    nA, nB = len(SA), len(SB)
    n = 2 * m + nA + nB
    adj = [set() for _ in range(n)]
    side = [0] * m + [1] * m + [0] * nA + [1] * nB
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            adj[x].add(m + L)
            adj[m + L].add(x)
    for t, j in enumerate(SB):
        y = 2 * m + nA + t
        for Q in line_points[j]:
            adj[y].add(Q)
            adj[Q].add(y)
    return n, adj, side


def _to_edges(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _candidates(d, rng, deadline):
    """Yield (n, adj, side) for each prime power q with q + 1 <= d (including the bare plane)."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg(q)
        SA, SB = [], []
        if s >= 1:
            SA = _pack(m, s, point_lines, rng, 40, deadline)
            SB = _pack(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs
        out.append(_assemble(m, edges, point_lines, line_points, SA, SB))
    return out


def _reach_ok(x, adj, D):
    """True if a BFS from x within D steps reaches every vertex."""
    dist = {x: 0}
    frontier = [x]
    for k in range(1, D + 1):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if v not in dist:
                    dist[v] = k
                    nxt.append(v)
        frontier = nxt
        if not frontier:
            break
    return len(dist) == len(adj)


def _grow(n, adj, side, d, D, deadline, rng):
    """Repeatedly try to add one vertex by greedy cover of the opposite side. Mutates adj, side."""
    while time.monotonic() < deadline:
        s = rng.randrange(2)
        pool = [v for v in range(n) if side[v] != s and len(adj[v]) < d]
        if not pool:
            s = 1 - s
            pool = [v for v in range(n) if side[v] != s and len(adj[v]) < d]
            if not pool:
                break
        rng.shuffle(pool)
        uncovered = {v for v in range(n) if side[v] == s}
        chosen = []
        chosen_set = set()
        while uncovered and len(chosen) < d:
            gains = []
            for v in pool:
                if v in chosen_set:
                    continue
                g = len(adj[v] & uncovered)
                if g > 0:
                    gains.append((g, v))
            if not gains:
                break
            top = max(g for g, _ in gains)
            if rng.random() < 0.2:
                _, v = rng.choice(gains)
            else:
                v = next(v for g, v in gains if g == top)
            chosen.append(v)
            chosen_set.add(v)
            uncovered -= adj[v]
        if uncovered or not chosen:
            continue
        x = len(adj)
        adj.append(set(chosen))
        side.append(s)
        for v in chosen:
            adj[v].add(x)
        if _reach_ok(x, adj, D):
            n += 1
        else:
            adj.pop()
            side.pop()
            for v in chosen:
                adj[v].discard(x)
    return n


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

    if D >= 3:
        # Arc-extended plane graphs, then generic vertex growth on the largest one.
        cands = _candidates(d, rng, start + 0.1 * time_limit)
        if cands:
            for n_c, adj_c, _side in cands:
                if n_c > best_n:
                    consider(n_c, _to_edges(adj_c))
            n_g, adj_g, side_g = max(cands, key=lambda t: t[0])
            n_g = _grow(n_g, adj_g, side_g, d, D, start + 0.55 * time_limit, rng)
            if n_g > best_n:
                consider(n_g, _to_edges(adj_g))

    if D >= 4 and time.monotonic() < start + 0.6 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts with the remaining time.
    deadline = start + 0.72 * time_limit
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
