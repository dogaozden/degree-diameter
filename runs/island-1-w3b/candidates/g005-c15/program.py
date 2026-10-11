import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic bases: projective planes, Araujo-Pardo-Lopez, generalized quadrangle.
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
# Shared graph utilities.
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


# ----------------------------------------------------------------------------
# Diameter-preserving growth: cover-based vertex extension and edge saturation.
# A new vertex joined to a set C covers v within D iff some c in C is within D-1
# of v, so greedy set cover over radius-(D-1) balls keeps the diameter bound.
# ----------------------------------------------------------------------------

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
    """Greedily join deficient opposite-side vertices in random order (only shortens distances)."""
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
    """Alternate cover-extension and saturation while either still makes progress."""
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


def _grow_multi(n, edges, d, D, end, seed, tries=4):
    """Run randomized _grow attempts until `end`, keeping the largest result.

    _grow often stops early when it makes no progress; the unused time is then
    given to the following attempts, so no slice is wasted.
    """
    best = (n, list(edges))
    for t in range(tries):
        now = time.monotonic()
        if now >= end:
            break
        slice_end = now + (end - now) / (tries - t)
        n2, e2 = _grow(n, edges, d, D, slice_end, random.Random(seed + 101 * t))
        if n2 > best[0]:
            best = (n2, e2)
    return best


# ----------------------------------------------------------------------------
# Cover-greedy growth from sparse cycle seeds (a construction independent of
# the algebraic bases): a cycle of length 2L has diameter L <= D and leaves
# degree slack everywhere, so greedy cover growth fills the slack.
# ----------------------------------------------------------------------------

def _cycle_seed(L):
    """Bipartite even cycle C_{2L} as (n, edges); diameter L."""
    N = 2 * L
    return N, [(i, (i + 1) % N) for i in range(N)]


# ----------------------------------------------------------------------------
# Iterated ruin-and-recreate on a valid graph.
#
# Each step deletes a clustered set of 1-3 vertices (a random vertex plus
# neighbours), frees their degree on the survivors, repairs with edge
# saturation and cover extension, and keeps the result only if it is still
# valid and at least as large. Equal-size moves are accepted, so the search
# drifts across the plateau of same-order graphs instead of stalling.
# ----------------------------------------------------------------------------

def _ruin_recreate(n, edges, d, D, deadline, rng):
    """Return the largest valid graph found by iterated ruin-and-recreate from (n, edges)."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        if cur_n < 4:
            break
        adj = [[] for _ in range(cur_n)]
        for u, v in cur_e:
            adj[u].append(v)
            adj[v].append(u)
        r = rng.choice([1, 1, 2, 2, 3])
        R = {rng.randrange(cur_n)}
        for _ in range(4 * r):
            if len(R) >= r:
                break
            u = rng.choice(list(R))
            nb = [w for w in adj[u] if w not in R]
            if nb:
                R.add(rng.choice(nb))
        keep = [v for v in range(cur_n) if v not in R]
        if not keep:
            continue
        remap = {old: i for i, old in enumerate(keep)}
        n2 = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u in remap and v in remap]
        e2 = _saturate_edges(n2, e2, d, rng)
        slice_end = min(deadline, time.monotonic() + 0.5)
        n3, e3 = _extend_cover(n2, e2, d, D, slice_end, rng)
        e3 = _saturate_edges(n3, e3, d, rng)
        if n3 >= cur_n and lib.is_valid(n3, e3, d, D):
            cur_n, cur_e = n3, e3
            if cur_n > best_n:
                best_n, best_e = cur_n, list(cur_e)
    return best_n, best_e


# ----------------------------------------------------------------------------
# NEW: Z_2 two-lift search of a valid base graph.
#
# A 2-lift doubles the order and preserves degree: every base edge (u, v) gets
# a sign s in {0, 1}, and the two copies (u, a), (v, a+s) are joined for a in
# {0, 1}. Copies keep the colour of their base vertex, so the lift stays
# bipartite. Signs are annealed to minimise the number of pairs farther apart
# than D; a zero-cost sign assignment is a valid graph of twice the order.
# ----------------------------------------------------------------------------

def _bad_cost(N, adj, D):
    """Number of ordered vertex pairs at distance > D (zero iff diameter <= D and connected)."""
    balls = _balls_radius(N, adj, D)
    return sum(N - b.bit_count() for b in balls)


def _two_lift_search(n, edges, d, D, deadline, rng):
    """Anneal Z_2 signs on the base graph so its 2-lift has diameter <= D; returns (N, edges) or None."""
    base = sorted({(min(u, v), max(u, v)) for u, v in edges if u != v})
    if not base:
        return None
    sign = [rng.randrange(2) for _ in base]

    def lift(sg):
        N = 2 * n
        E = []
        for (u, v), s in zip(base, sg):
            for a in (0, 1):
                E.append((u + a * n, v + ((a + s) & 1) * n))
        adj2 = [[] for _ in range(N)]
        for x, y in E:
            adj2[x].append(y)
            adj2[y].append(x)
        return N, E, adj2

    N, E, adj2 = lift(sign)
    cost = _bad_cost(N, adj2, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while cost > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        T = 0.5 * (0.02 ** frac)
        i = rng.randrange(len(base))
        sign[i] ^= 1
        N2, E2, adj3 = lift(sign)
        c2 = _bad_cost(N2, adj3, D)
        u = 1.0 - rng.random()
        if c2 <= cost - T * math.log(u):
            cost = c2
            E = E2
        else:
            sign[i] ^= 1
    if cost == 0:
        return N, E
    return None


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
# Haar graph hill-climb (small D).
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


# ----------------------------------------------------------------------------
# Unstructured bipartite 2-switch local search (heavy targets, final phase).
# Degrees are preserved by 2-switches, so the degree bound is never violated.
# ----------------------------------------------------------------------------

def _bip_search(d, D, N, rng, deadline):
    """Try to find a bipartite graph on N vertices, max degree d, diameter <= D by 2-switch annealing."""
    h = N // 2
    if h < d + 1:
        return None
    adj = [[] for _ in range(N)]
    E = set()
    for _ in range(d):
        perm = list(range(h))
        rng.shuffle(perm)
        for a in range(h):
            b = h + perm[a]
            if (a, b) not in E and len(adj[a]) < d and len(adj[b]) < d:
                E.add((a, b))
                adj[a].append(b)
                adj[b].append(a)
    edges = list(E)
    if len(edges) < 2:
        return None

    cost = _bad_cost(N, adj, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = 0.6 * (0.03 ** frac)
        i = rng.randrange(len(edges))
        j = rng.randrange(len(edges))
        if i == j:
            continue
        a1, b1 = edges[i]
        a2, b2 = edges[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in E or (a2, b1) in E:
            continue
        E.discard((a1, b1)); E.discard((a2, b2))
        E.add((a1, b2)); E.add((a2, b1))
        adj[a1].remove(b1); adj[b1].remove(a1)
        adj[a2].remove(b2); adj[b2].remove(a2)
        adj[a1].append(b2); adj[b2].append(a1)
        adj[a2].append(b1); adj[b1].append(a2)

        c2 = _bad_cost(N, adj, D)
        u = 1.0 - rng.random()
        if c2 <= cost - T * math.log(u):
            cost = c2
            edges[i] = (a1, b2)
            edges[j] = (a2, b1)
        else:
            E.discard((a1, b2)); E.discard((a2, b1))
            E.add((a1, b1)); E.add((a2, b2))
            adj[a1].remove(b2); adj[b2].remove(a1)
            adj[a2].remove(b1); adj[b1].remove(a2)
            adj[a1].append(b1); adj[b1].append(a1)
            adj[a2].append(b2); adj[b2].append(a2)

    if cost > 0:
        return None
    return N, [(a, b) for a, b in E]


def _search_regular(d, D, best_n, rng, deadline, consider):
    """Repeatedly search for larger unstructured graphs; `consider` returns the current best order."""
    def even(x):
        return x - (x % 2)

    cur = best_n
    N = even(int(cur * 1.05))
    while time.monotonic() < deadline - 0.5:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(1.0, 0.4 * remaining))
        g = _bip_search(d, D, N, rng, slice_end)
        if g is not None:
            n, e = g
            e = _saturate_edges(n, e, d, rng)
            cur = consider(n, e)
            N = even(int(cur * 1.03)) + 2
        else:
            N = even(max(cur + 2, int(N * 0.97)))


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
        return best_n

    T = time_limit
    heavy = D >= 4 and d >= 5
    # Time split: group-lift search, then Z_2 two-lift attempts, then
    # ruin-and-recreate, then (heavy only) the unstructured 2-switch tail.
    group_end = min(deadline, start + (0.55 * T if heavy else 0.75 * T))
    ils_end = min(deadline, start + 0.8 * T) if heavy else deadline

    # Algebraic bases, each grown by diameter-preserving extension (several
    # randomized growth attempts per base, keeping the largest valid result).
    if D >= 3 and best_n < moore:
        ara = _araujo_best(d)
        if ara is not None:
            consider(ara[0], ara[1])
            n2, e2 = _grow_multi(ara[0], ara[1], d, D, start + 0.15 * T, seed + 2)
            consider(n2, e2)
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow_multi(pg[0], pg[1], d, D, start + 0.25 * T, seed + 1)
            consider(n2, e2)
        for n_c, e_c in _arc_extensions(d, start + 0.35 * T,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 4 and best_n < moore and time.monotonic() < group_end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow_multi(gq[0], gq[1], d, D, start + 0.4 * T, seed + 3)
            consider(n2, e2)

    # Bold branch: construction independent of the algebraic bases. Greedy cover
    # growth from sparse cycle seeds (diameter L <= D, spare degree everywhere),
    # with randomized restarts. Every result still goes through consider().
    if D >= 4 and d >= 3 and best_n < moore:
        cover_end = min(group_end, start + (0.45 * T if heavy else 0.25 * T))
        restarts = 0
        while time.monotonic() < cover_end - 0.5 and best_n < moore and restarts < 60:
            restarts += 1
            L = D if rng.random() < 0.7 else max(2, D - 1)
            n0, e0 = _cycle_seed(L)
            now = time.monotonic()
            slice_end = min(cover_end, now + max(1.0, 0.5 * (cover_end - now)))
            n2, e2 = _grow(n0, e0, d, D, slice_end, rng)
            consider(n2, e2)

    # Main search: annealed group voltage lifts, with occasional Haar attempts for small D.
    # The group-size window widens after consecutive failures, so the search can reach
    # larger groups than the current best.
    ks = [1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    haar_m, haar_miss = d + 1, 0
    fails = 0
    while time.monotonic() < group_end and best_n < moore:
        if D <= 4 and haar_miss < 4 and rng.random() < 0.1:
            S = _search_haar(d, D, haar_m, rng, group_end, 120)
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
        res = _anneal(d, D, k, order, mul, rng, group_end,
                      run_secs=3.0, iters=400)
        if res is not None:
            consider(res[0], res[1])
            fails = 0
        else:
            fails += 1

    # NEW: Z_2 two-lift of the current best graph, with annealed signs.
    # Degree is preserved and the lift stays bipartite; saturation then fills
    # any slack left by deficient base vertices.
    if D >= 3 and best_n < moore and time.monotonic() < ils_end - 1.0:
        try:
            now = time.monotonic()
            lift_end = min(ils_end - 0.5, now + 0.3 * (ils_end - now))
            r2 = _two_lift_search(best_n, best[1], d, D, lift_end, rng)
            if r2 is not None:
                n3, e3 = r2
                e3 = _saturate_edges(n3, e3, d, rng)
                consider(n3, e3)
        except Exception:
            pass

    # Ruin-and-recreate refinement of the current best graph.
    if D >= 3 and best_n < moore and time.monotonic() < ils_end - 0.5:
        try:
            n_r, e_r = _ruin_recreate(best_n, best[1], d, D, ils_end, rng)
            consider(n_r, e_r)
        except Exception:
            pass

    # Heavy tail: unstructured 2-switch search to exceed the current best order.
    if heavy and time.monotonic() < deadline - 1.0 and best_n < moore:
        try:
            _search_regular(d, D, best_n, rng, deadline, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
