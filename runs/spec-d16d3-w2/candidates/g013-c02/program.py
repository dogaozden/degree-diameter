import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Each old vertex has degree q+1, so with d >= q+1 it has spare s = d-q-1.
# Pick an arc S of points (every line holds <= s points of S). For each P in S
# add an A-vertex joined to the q+1 lines through P; for each j in S add a
# B-vertex joined to the q+1 points on line j. Order 2(q^2+q+1) + 2|S|.
#
# New in this version: a hub-swap annealing search (D = 3, d >= 8). Its state
# may contain diameter violations; the objective is the number of bad pairs
# (lib.bad_pairs). Moves add a hub at a random pencil or line, first freeing a
# slot on each saturated neighbour by deleting one of its edges, or rewire one
# edge. Degrees stay <= d and bipartiteness is preserved by construction. The
# best state with zero bad pairs is kept and validated with lib.is_valid.
# ----------------------------------------------------------------------------

def _pg_data(q):
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


def _loads_ok(S, s, m, pl, lp):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, pl, lp, rng, trials, deadline):
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
            if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
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


def _arc_graph(m, edges, S, pl, lp):
    """Build the extended graph: old PG incidence plus A (point-side) and B (line-side) hubs per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return candidates (n, edges, m, pl, lp, k) for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, pl, lp):
            continue
        n_c, e_c = _arc_graph(m, edges, S, pl, lp)
        out.append((n_c, e_c, m, pl, lp, len(S)))
    return out


def _from_edges(n, E):
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _elist(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _swap_search(n0, E0, m, pl, lp, k, d, D, deadline, rng):
    """Annealing over hub insertions and edge rewires; objective = number of bad pairs."""
    side0 = [0] * m + [1] * m + [0] * k + [1] * k
    adj = _from_edges(n0, E0)
    side = list(side0)
    bad = lib.bad_pairs(n0, E0, D)
    best_n, best_E, best_side = n0, list(E0), list(side0)
    T, stale = 2.0, 0

    while time.monotonic() < deadline:
        stale += 1
        T = max(0.3, T * 0.9995)
        if stale > 1500:
            # Restart from the best valid state.
            adj = _from_edges(best_n, best_E)
            side = list(best_side)
            bad = 0
            T, stale = 2.0, 0
        N = len(adj)

        if rng.random() < 0.5:
            # Insert a hub: a pencil (point-side) or a line's points (line-side).
            if rng.random() < 0.5:
                nbrs = [m + L for L in pl[rng.randrange(m)]]
                sd = 0
            else:
                nbrs = list(lp[rng.randrange(m)])
                sd = 1
            removed = []
            for u in nbrs:
                if len(adj[u]) >= d:
                    w = rng.choice(sorted(adj[u]))
                    adj[u].discard(w)
                    adj[w].discard(u)
                    removed.append((u, w))
            adj.append(set(nbrs))
            side.append(sd)
            for u in nbrs:
                adj[u].add(N)
            new_bad = lib.bad_pairs(N + 1, _elist(adj), D)
            delta = new_bad - bad
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                bad = new_bad
            else:
                for u in nbrs:
                    adj[u].discard(N)
                adj.pop()
                side.pop()
                for u, w in removed:
                    adj[u].add(w)
                    adj[w].add(u)
                continue
        else:
            # Rewire: drop one edge, then join a random pair of vertices with spare degree.
            s0 = [v for v in range(N) if side[v] == 0 and adj[v]]
            if not s0:
                continue
            u = rng.choice(s0)
            w = rng.choice(sorted(adj[u]))
            adj[u].discard(w)
            adj[w].discard(u)
            a_c = [v for v in range(N) if side[v] == 0 and len(adj[v]) < d]
            b_c = [v for v in range(N) if side[v] == 1 and len(adj[v]) < d]
            pick = None
            if a_c and b_c:
                for _ in range(30):
                    a = rng.choice(a_c)
                    b = rng.choice(b_c)
                    if b not in adj[a]:
                        pick = (a, b)
                        break
            if pick is None:
                adj[u].add(w)
                adj[w].add(u)
                continue
            a, b = pick
            adj[a].add(b)
            adj[b].add(a)
            new_bad = lib.bad_pairs(N, _elist(adj), D)
            delta = new_bad - bad
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                bad = new_bad
            else:
                adj[a].discard(b)
                adj[b].discard(a)
                adj[u].add(w)
                adj[w].add(u)
                continue

        if bad == 0 and len(adj) > best_n:
            best_n = len(adj)
            best_E = _elist(adj)
            best_side = list(side)
            stale = 0

    if best_n > n0:
        return best_n, best_E
    return None


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

    swap_done = False
    if D >= 3:
        cands = _arc_extensions(d, start + 0.2 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for c in cands:
            consider(c[0], c[1])

        # New: hub-swap annealing from the largest arc graph (D = 3, larger degrees).
        if cands and d >= 8 and D == 3:
            n_c, e_c, m, pl, lp, k = cands[0]
            res = _swap_search(n_c, e_c, m, pl, lp, k, d, D,
                               start + 0.85 * time_limit, random.Random(seed * 31 + 7))
            swap_done = True
            if res is not None:
                consider(res[0], res[1])

    if D >= 4 and time.monotonic() < start + 0.5 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts for the remaining cases.
    if not swap_done:
        deadline = start + 0.8 * time_limit
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
