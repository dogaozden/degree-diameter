import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare capacity
# s = d - q - 1. Choose a point set S such that every line contains at most s
# points of S and every point lies on at most s lines indexed by S. For each
# P in S add a new A-vertex joined to all q+1 lines through P; for each j in S
# add a new B-vertex joined to all q+1 points on line j. Diameter stays 3.
#
# New in this version: the set S is found by a local search (add a point and
# evict the few conflicting members) in addition to randomized greedy, so
# larger admissible sets are found when greedy stalls.
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


def _arc_local_search(m, s, point_lines, line_points, rng, deadline, iters):
    """Local search for a large S with loads <= s.

    Pick a point P outside S, evict the members of S that block it (the S-points on
    full lines through P and the S-lines through full points on line P), then add P.
    Moves with at most one eviction are always taken; larger ones are taken with a
    decaying Boltzmann probability.
    """
    inS = [False] * m
    cl = [0] * m
    cp = [0] * m
    S = set()
    best = []

    def add(x):
        inS[x] = True
        S.add(x)
        for L in point_lines[x]:
            cl[L] += 1
        for Q in line_points[x]:
            cp[Q] += 1

    def remove(x):
        inS[x] = False
        S.discard(x)
        for L in point_lines[x]:
            cl[L] -= 1
        for Q in line_points[x]:
            cp[Q] -= 1

    for it in range(iters):
        if time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        R = set()
        for L in point_lines[P]:
            if cl[L] >= s:
                for Q in line_points[L]:
                    if inS[Q]:
                        R.add(Q)
        for Q in line_points[P]:
            if cp[Q] >= s:
                for j in point_lines[Q]:
                    if inS[j]:
                        R.add(j)
        temp = max(0.1, 0.6 * (1.0 - it / iters))
        if len(R) <= 1 or rng.random() < math.exp(-(len(R) - 1) / temp):
            for x in R:
                remove(x)
            add(P)
            if len(S) > len(best):
                best = sorted(S)
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, S, line_points):
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):  # S is also a set of line indices (same vectors)
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
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
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 20, deadline))
            sub = min(deadline, time.monotonic() + 1.5)
            cands.append(_arc_local_search(m, s, point_lines, line_points, rng, sub, 6000))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, S, line_points)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Neighbourhood annealing for one extra vertex (any D >= 3).
#
# New idea: instead of greedy covers, anneal the neighbourhood T of a new vertex
# x on a chosen side. The cost is the number of vertices not within distance D of
# x (old pairs are already fine, so only pairs involving x matter). Moves add,
# remove, or swap neighbours, subject to the degree cap on both x and each
# neighbour. Any result is double-checked with lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """2-colouring of a bipartite graph given by adjacency lists."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _reach(x, adj, D):
    """Number of vertices within distance D of x (including x)."""
    seen = {x}
    frontier = [x]
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if v not in seen:
                    seen.add(v)
                    nxt.append(v)
        if not nxt:
            break
        frontier = nxt
    return len(seen)


def _grow_vertex(n, edges, d, D, side, deadline, rng, iters):
    """Try to add one vertex on `side` by annealing its neighbourhood; return (n+1, edges) or None."""
    adj = [set() for _ in range(n + 1)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _bipartition(n, [list(a) for a in adj[:n]])
    x = n
    T = adj[x]
    opp = [v for v in range(n) if col[v] == 1 - side and len(adj[v]) < d]
    if not opp:
        return None

    def toggle(t, on):
        if on:
            adj[t].add(x)
            T.add(t)
        else:
            adj[t].discard(x)
            T.discard(t)

    def cost():
        return n + 1 - _reach(x, adj, D)

    # Greedy start: add the sampled candidate that most reduces the cost.
    for _ in range(d):
        cands = [t for t in opp if t not in T and len(adj[t]) < d]
        if not cands:
            break
        sample = rng.sample(cands, min(12, len(cands)))
        bt, bc = None, None
        for t in sample:
            toggle(t, True)
            c = cost()
            toggle(t, False)
            if bc is None or c < bc:
                bt, bc = t, c
        toggle(bt, True)
        if bc == 0:
            break

    cur = cost()
    temp = 1.0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, temp * 0.997)
        r = rng.random()
        undo = []
        if r < 0.35 and len(T) < d:
            t = rng.choice(opp)
            if t in T or len(adj[t]) >= d:
                continue
            toggle(t, True)
            undo.append((t, False))
        elif r < 0.6 and T:
            t = rng.choice(list(T))
            toggle(t, False)
            undo.append((t, True))
        else:
            if not T:
                continue
            t_out = rng.choice(list(T))
            t_in = rng.choice(opp)
            if t_in in T or t_in == t_out or len(adj[t_in]) >= d:
                continue
            toggle(t_out, False)
            undo.append((t_out, True))
            toggle(t_in, True)
            undo.append((t_in, False))
        new = cost()
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
        else:
            for t, on in reversed(undo):
                toggle(t, on)

    if cur != 0:
        return None
    new_edges = list(edges) + [(t, x) for t in T]
    if lib.is_valid(n + 1, new_edges, d, D):
        return n + 1, new_edges
    return None


def _grow_loop(n, edges, d, D, deadline, rng):
    """Repeatedly add vertices with _grow_vertex until several attempts in a row fail."""
    fails = 0
    while time.monotonic() < deadline and fails < 8:
        res = _grow_vertex(n, edges, d, D, rng.randrange(2), deadline, rng, 1500)
        if res is None:
            fails += 1
        else:
            n, edges = res
            fails = 0
    return n, edges


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

    if D >= 3:
        # Arc-extended projective plane graphs (valid for all D >= 3).
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

        # New: grow extra vertices by annealing their neighbourhoods on top of the best graph.
        if best_n > 2 and time.monotonic() < deadline:
            n_g, e_g = _grow_loop(best_n, list(best[1]), d, D, deadline,
                                  random.Random(seed * 104729 + d))
            consider(n_g, e_g)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts, for D >= 4 only (they never beat the D = 3 constructions).
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
