import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Known bases: Araujo-Pardo-Lopez, projective plane, generalized quadrangle.
# ----------------------------------------------------------------------------

def _araujo_best(d):
    """Araujo-Pardo-Lopez graph for the largest prime power q <= d - 2 (degree q + 2 <= d, diameter 3)."""
    for q in range(min(d - 2, 23), 2, -1):
        if lib.is_prime_power(q):
            try:
                return lib.araujo_lopez_graph(q)
            except ValueError:
                return None
    return None


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
# NEW: twin cloning (diameter-preserving, degree-respecting growth).
#
# A clone w of vertex v gets exactly the neighbourhood N(v). Every neighbour
# of v gains one degree, so cloning is allowed only when all of N(v) has spare
# degree. For x not in {v, w}, dist(w, x) = dist(v, x) because N(w) = N(v), and
# dist(v, w) = 2. So the diameter is unchanged. w sits on v's side of the
# bipartition, so the graph stays bipartite. Each clone consumes slack, so the
# process terminates. Clones of clones are allowed too.
# ----------------------------------------------------------------------------

def _clone_grow(n, edges, d, deadline, rng):
    """Repeatedly add twins of vertices whose whole neighbourhood still has spare degree."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        order = list(range(n))
        rng.shuffle(order)
        for v in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[v]
            if not nb or len(nb) > d or any(deg[u] >= d for u in nb):
                continue
            w = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for u in nb:
                adj[u].append(w)
                deg[u] += 1
                edges.append((u, w))
            grew = True
    return n, edges


# ----------------------------------------------------------------------------
# Cover-based vertex extension and edge saturation (diameter-preserving growth).
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of the graph."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices first, then saturate edges with the leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Overshoot-and-repair growth.
#
# Add a vertex whose d neighbours cover all but a few vertices within D-1
# (partial cover), then repair the resulting diameter defects with
# degree-preserving swaps and slack-moving rewires. A move is kept only if the
# number of bad (over-distance) pairs does not increase. Rejected rounds are
# rolled back exactly.
# ----------------------------------------------------------------------------

def _set_edge(adj, a, b, on):
    """Add or remove the undirected edge {a, b} in set-based adjacency."""
    if on:
        adj[a].add(b)
        adj[b].add(a)
    else:
        adj[a].discard(b)
        adj[b].discard(a)


def _bad_count(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (unreachable counted)."""
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _partial_pick(cands, ball, d, rng):
    """Greedy pick of up to d candidates maximising coverage; returns (chosen, covered mask)."""
    pool = list(cands)
    covered = 0
    chosen = []
    for _ in range(d):
        if not pool:
            break
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains)
        if best_g <= 0:
            break
        opts = [i for i, g in enumerate(gains) if g == best_g]
        s = pool.pop(rng.choice(opts))
        chosen.append(s)
        covered |= ball[s]
    return chosen, covered


def _rewire_repair(n, adj, color, el, d, D, deadline, rng, max_iters):
    """Local search on bipartite edges el (pairs (side0, side1)) that lowers bad pairs.

    Moves: degree-preserving 2-swaps, and moving one endpoint of an edge to a
    deficient vertex on the same side. A move is kept iff bad count does not rise.
    Returns True when the graph has no bad pairs.
    """
    side1 = [v for v in range(n) if color[v] == 1]
    cur = _bad_count(n, adj, D)
    it = 0
    while cur > 0 and it < max_iters and time.monotonic() < deadline:
        it += 1
        if len(el) < 2:
            break
        if rng.random() < 0.5:
            i = rng.randrange(len(el))
            j = rng.randrange(len(el))
            if i == j:
                continue
            l1, r1 = el[i]
            l2, r2 = el[j]
            if l1 == l2 or r1 == r2 or r2 in adj[l1] or r1 in adj[l2]:
                continue
            _set_edge(adj, l1, r1, False)
            _set_edge(adj, l2, r2, False)
            _set_edge(adj, l1, r2, True)
            _set_edge(adj, l2, r1, True)
            new = _bad_count(n, adj, D)
            if new <= cur:
                cur = new
                el[i] = (l1, r2)
                el[j] = (l2, r1)
            else:
                _set_edge(adj, l1, r2, False)
                _set_edge(adj, l2, r1, False)
                _set_edge(adj, l1, r1, True)
                _set_edge(adj, l2, r2, True)
        else:
            deficient = [v for v in side1 if len(adj[v]) < d]
            if not deficient:
                break
            i = rng.randrange(len(el))
            l, r = el[i]
            c = rng.choice(deficient)
            if c == r or c in adj[l]:
                continue
            _set_edge(adj, l, r, False)
            _set_edge(adj, l, c, True)
            new = _bad_count(n, adj, D)
            if new <= cur:
                cur = new
                el[i] = (l, c)
            else:
                _set_edge(adj, l, c, False)
                _set_edge(adj, l, r, True)
    return cur == 0


def _overshoot_repair(n, edges, d, D, deadline, rng, consider):
    """Repeatedly add a partially-covering vertex and repair; report each valid success."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _bipartition(n, adj)
    el = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    cur_n = n
    for _ in range(60):
        if time.monotonic() >= deadline:
            break
        snap = (cur_n, [set(a) for a in adj], list(el), list(color))
        ball = _balls_radius(cur_n, adj, D - 1)
        full = (1 << cur_n) - 1
        c = rng.randrange(2)
        cands = [s for s in range(cur_n) if color[s] == c and len(adj[s]) < d]
        if not cands:
            c = 1 - c
            cands = [s for s in range(cur_n) if color[s] == c and len(adj[s]) < d]
        if not cands:
            break
        chosen, covered = _partial_pick(cands, ball, d, rng)
        uncovered = (full & ~covered).bit_count()
        if not chosen or uncovered > 3 + cur_n // 100:
            break
        v = cur_n
        cur_n += 1
        adj.append(set())
        color.append(1 - c)
        for s in chosen:
            _set_edge(adj, s, v, True)
            el.append((s, v) if c == 0 else (v, s))
        if _rewire_repair(cur_n, adj, color, el, d, D, deadline, rng, 150):
            consider(cur_n, [(a, b) for a, b in el])
        else:
            cur_n, adj, el, color = snap[0], snap[1], snap[2], snap[3]
            break


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
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


def _anneal(d, D, k, G, mul, rng, deadline, run_secs, iters):
    """Simulated annealing over voltages and per-layer B-assignments.

    The temperature falls geometrically from 1.0 to 0.05 with the larger of
    iteration progress and wall-clock progress. A move with new cost c2 is
    accepted iff c2 <= cost - T*ln(u), u ~ Uniform(0, 1]; that threshold is
    also the early-exit limit for the cost evaluation.
    """
    t0 = time.monotonic()
    end = min(deadline, t0 + run_secs)
    span = max(1e-6, end - t0)

    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for it in range(iters):
        if cost == 0:
            break
        now = time.monotonic()
        if now >= end:
            break
        frac = max(it / iters, (now - t0) / span)
        T = 0.05 ** min(1.0, frac)
        u = 1.0 - rng.random()  # in (0, 1]
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
    # Use more of the budget: the final validity check is cheap relative to a 3 s margin.
    deadline = start + max(0.5, min(0.9 * time_limit, time_limit - 3.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    def consider_clone(n, e, s):
        """Twin-clone growth of a candidate, then consider the result."""
        if time.monotonic() >= deadline:
            return
        n2, e2 = _clone_grow(n, e, d, deadline, random.Random(s))
        if n2 > n:
            consider(n2, e2)

    if D >= 3 and best_n < moore:
        # Araujo-Pardo-Lopez record base (degree q + 2 <= d), grown if possible.
        ara = _araujo_best(d)
        if ara is not None:
            consider(ara[0], ara[1])
            consider_clone(ara[0], ara[1], seed + 11)
            n2, e2 = _grow(ara[0], ara[1], d, D, start + 0.15 * time_limit,
                           random.Random(seed + 2))
            consider(n2, e2)
            consider_clone(n2, e2, seed + 12)
        # Plain projective plane, grown by cover extension and saturation.
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            consider_clone(pg[0], pg[1], seed + 13)
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.25 * time_limit,
                           random.Random(seed + 1))
            consider(n2, e2)
            consider_clone(n2, e2, seed + 14)
        # Arc-extended projective plane graphs.
        for n_c, e_c in _arc_extensions(d, start + 0.35 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)
            consider_clone(n_c, e_c, seed + 15)

    if D >= 4 and best_n < moore and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            consider_clone(gq[0], gq[1], seed + 16)
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.4 * time_limit, rng)
            consider(n2, e2)
            consider_clone(n2, e2, seed + 17)

    # Overshoot-and-repair on the current best graph (D >= 3 only).
    if D >= 3 and best_n < moore and time.monotonic() < start + 0.5 * time_limit:
        try:
            _overshoot_repair(best_n, best[1], d, D, start + 0.5 * time_limit,
                              random.Random(seed + 3), consider)
        except Exception:
            pass
        consider_clone(best[0], best[1], seed + 18)

    # Main search: annealed group voltage lifts, with occasional Haar attempts for small D.
    # The group-size window widens after consecutive failures, so the search can reach
    # larger groups than the current best (records often need |G| well above best/(2k)).
    # Annealing budget also grows with consecutive failures: larger groups have costlier
    # evaluations, so a short anneal can end before reaching cost 0 even when a lift exists.
    ks = [1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    haar_m, haar_miss = d + 1, 0
    fails = 0
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
        base = best_n // (2 * k)
        spread = min(0.6, 0.04 * (1 + fails))
        hi = max(base // 8 + 1, int(base * spread))
        G = max(2, base + 1 + rng.randrange(0, hi))
        g = _sample_group(G, rng)
        if g is None:
            fails += 1
            continue
        order, mul = g
        # Budget scales with failures, capped at 4x the base anneal (about 12 s per attempt).
        scale = 1 + min(3, fails // 4)
        res = _anneal(d, D, k, order, mul, rng, deadline,
                      run_secs=3.0 * scale, iters=400 * scale)
        if res is not None:
            consider(res[0], res[1])
            consider_clone(res[0], res[1], seed + 19 + fails)
            fails = 0
        else:
            fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
