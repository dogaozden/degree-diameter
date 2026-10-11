import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Helpers: projective plane, generalized quadrangle and Araujo-Pardo-Lopez bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_best(d):
    """Araujo-Pardo-Lopez graph for the largest prime power q <= d - 2 (degree q + 2 <= d, diameter 3)."""
    for q in range(min(d - 2, 23), 2, -1):
        if lib.is_prime_power(q):
            try:
                return lib.araujo_lopez_graph(q)
            except ValueError:
                return None
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
# Twin cloning (diameter- and bipartiteness-preserving blow-up).
#
# Cloning a vertex u creates v with N(v) = N(u). v sits on u's side, so the graph
# stays bipartite. Any shortest path through v can be rerouted through u, so old
# distances are unchanged; d(v, x) = d(u, x) for x != u, and d(v, u) = 2. Hence the
# diameter is preserved whenever D >= 2. Spare degree of the neighbours of u
# limits how many clones u can take.
# ----------------------------------------------------------------------------

def _twin_fill(n, edges, d):
    """Repeatedly clone vertices while their neighbours have spare degree. Returns (n, edges)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    changed = True
    while changed:
        changed = False
        for u in range(len(adj)):
            nb = adj[u]
            if not nb or len(nb) > d:
                continue
            cap = min(d - deg[w] for w in nb)
            for _ in range(cap):
                v = len(adj)
                adj.append(list(nb))
                deg.append(len(nb))
                for w in nb:
                    adj[w].append(v)
                    deg[w] += 1
                changed = True
    out = []
    for v in range(len(adj)):
        for w in adj[v]:
            if w > v:
                out.append((v, w))
    return len(adj), out


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
# Cover-based vertex extension (diameter-preserving growth).
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
# Pair insertion with switch-based repair.
#
# Insert two new vertices x (side 0) and y (side 1) into a graph of max degree d.
# Pick d edges (a_i, b_i) with pairwise distinct endpoints, delete them, and add
# x-b_i and y-a_i. Every old degree is unchanged and x, y reach degree d, so the
# graph stays bipartite with max degree d. Diameter is then restored by
# degree-preserving 2-switches, annealed on the number of ordered pairs at
# distance > D.
# ----------------------------------------------------------------------------

def _bad_count(n, adj, D):
    """Number of ordered vertex pairs at distance > D (zero iff connected with diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _insert_and_repair(n, edges, d, D, deadline, rng, tries=3, anneal_iters=300):
    """Return (n+2, edges) with diameter <= D, or None if repair fails in time."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _bipartition(n, [list(s) for s in adj])
    Eo = [(u, v) if col[u] == 0 else (v, u) for u, v in edges]

    best_state = None
    best_c = None
    for _ in range(tries):
        if time.monotonic() >= deadline:
            break
        rng.shuffle(Eo)
        used_a, used_b, pick = set(), set(), []
        for a, b in Eo:
            if a not in used_a and b not in used_b:
                pick.append((a, b))
                used_a.add(a)
                used_b.add(b)
                if len(pick) == d:
                    break
        if len(pick) < d:
            continue
        adj2 = [set(s) for s in adj] + [set(), set()]
        x, y = n, n + 1
        for a, b in pick:
            adj2[a].discard(b)
            adj2[b].discard(a)
            adj2[x].add(b)
            adj2[b].add(x)
            adj2[y].add(a)
            adj2[a].add(y)
        c = _bad_count(n + 2, adj2, D)
        if best_c is None or c < best_c:
            best_c, best_state = c, adj2
        if best_c == 0:
            break
    if best_state is None:
        return None

    n2 = n + 2
    adj2 = best_state
    c = best_c
    col2 = col + [0, 1]
    E = [[a, b] for a in range(n2) if col2[a] == 0 for b in adj2[a]]
    if len(E) < 2:
        return None

    for it in range(anneal_iters):
        if c == 0 or time.monotonic() >= deadline:
            break
        i, j = rng.sample(range(len(E)), 2)
        a, b = E[i]
        cc, dd = E[j]
        if a == cc or b == dd or dd in adj2[a] or b in adj2[cc]:
            continue
        adj2[a].discard(b)
        adj2[b].discard(a)
        adj2[cc].discard(dd)
        adj2[dd].discard(cc)
        adj2[a].add(dd)
        adj2[dd].add(a)
        adj2[cc].add(b)
        adj2[b].add(cc)
        c2 = _bad_count(n2, adj2, D)
        T = 4.0 * (0.05 ** (it / anneal_iters))
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            E[i] = [a, dd]
            E[j] = [cc, b]
            c = c2
        else:
            adj2[a].discard(dd)
            adj2[dd].discard(a)
            adj2[cc].discard(b)
            adj2[b].discard(cc)
            adj2[a].add(b)
            adj2[b].add(a)
            adj2[cc].add(dd)
            adj2[dd].add(cc)

    if c != 0:
        return None
    out = [(a, b) for a in range(n2) if col2[a] == 0 for b in adj2[a]]
    return n2, out


def _repair_growth(n, edges, d, D, deadline, rng, consider):
    """Repeatedly insert vertex pairs with repair; stop after 3 consecutive failures."""
    fails = 0
    while time.monotonic() < deadline and fails < 3:
        res = _insert_and_repair(n, edges, d, D, deadline, rng)
        if res is None:
            fails += 1
            continue
        fails = 0
        n, edges = res
        consider(n, edges)
    return n, edges


# ----------------------------------------------------------------------------
# NEW: twin-shuffle plateau search (ruin-and-recreate on twin classes).
#
# Two vertices u, v on the same side with identical neighbourhoods are twins.
# Deleting one of them leaves every distance among the survivors unchanged
# (any path through v is rerouted through u), so the graph stays valid with
# max degree d and diameter <= D. Deleting v also frees one unit of degree on
# each neighbour of v. The move then re-spends the freed capacity: a cover
# extension may add a vertex back (possibly in a different place), edges are
# saturated, and twins are cloned again. Moves that shrink the order are
# rejected; moves that keep the order are accepted as a plateau walk, which
# changes the structure without losing size. Only strict improvements are
# handed to `consider`.
# ----------------------------------------------------------------------------

def _twin_remove_once(n, edges, rng):
    """Delete one random vertex that has a twin (same nonempty neighbourhood). Returns (n-1, edges) or None."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    groups = {}
    for v in range(n):
        if adj[v]:
            groups.setdefault(frozenset(adj[v]), []).append(v)
    cands = [g for g in groups.values() if len(g) >= 2]
    if not cands:
        return None
    grp = rng.choice(cands)
    v = rng.choice(grp)
    for w in adj[v]:
        adj[w].discard(v)
    adj[v] = set()
    last = n - 1
    if v != last:
        # Relabel the last vertex into the freed slot v (no edge to v remains).
        for w in adj[last]:
            adj[w].discard(last)
            adj[w].add(v)
        adj[v] = adj[last]
    adj.pop()
    n2 = n - 1
    out = [(u, w) for u in range(n2) for w in adj[u] if u < w]
    return n2, out


def _ruin_recreate(n, edges, d, D, deadline, rng):
    """One twin-removal followed by diameter-preserving re-growth. Returns (n2, edges) or None."""
    removed = _twin_remove_once(n, edges, rng)
    if removed is None:
        return None
    n1, e1 = removed
    n2, e2 = _extend_cover(n1, e1, d, D, deadline, rng)
    e2 = _saturate_edges(n2, e2, d, rng)
    if n2 >= n:
        n2, e2 = _twin_fill(n2, e2, d)
    return n2, e2


def _plateau_search(n, edges, d, D, deadline, rng, consider):
    """Walk over graphs of order >= current order via twin ruin-and-recreate; report strict gains."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        step_deadline = min(deadline, time.monotonic() + 1.0)
        res = _ruin_recreate(cur_n, cur_e, d, D, step_deadline, rng)
        if res is None:
            break
        n2, e2 = res
        if n2 >= cur_n:
            grew = n2 > cur_n
            cur_n, cur_e = n2, e2
            if grew:
                consider(cur_n, cur_e)
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k, annealed.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# Left multiplication by any group element is an automorphism, so representatives
# at the identity suffice for the distance check.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _groups_of_order(G, rng, cap=8):
    """All semidirect products Z_m x| Z_k2 of order G (sampled down to `cap` multipliers each)."""
    out = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            rs = [1]
        else:
            rs = [r for r in range(1, m)
                  if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if len(rs) > cap:
                rs = rng.sample(rs, cap)
        for r in rs:
            try:
                order, mul, _ = lib.semidirect_group(m, k2, r)
            except ValueError:
                continue
            out.append((order, mul))
    return out


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
    """Simulated annealing over voltages and per-layer B-assignments.

    Metropolis acceptance is drawn up front: a move with new cost c2 is accepted
    iff c2 <= cost - T*ln(u) for u ~ Uniform(0, 1]. This threshold doubles as the
    early-exit limit for the cost evaluation.
    """
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
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
    main_deadline = start + 0.6 * time_limit
    repair_deadline = start + 0.7 * time_limit
    plateau_deadline = start + 0.9 * time_limit
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
        # Spend leftover spare degree on diameter-preserving twin clones first.
        if D >= 2 and n > 0:
            n, e = _twin_fill(n, e, d)
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        ara = _araujo_best(d)
        if ara is not None:
            consider(ara[0], ara[1])
            n2, e2 = _grow(ara[0], ara[1], d, D, start + 0.15 * time_limit, rng)
            consider(n2, e2)
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.25 * time_limit, rng)
            consider(n2, e2)
        for n_c, e_c in _arc_extensions(d, start + 0.30 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.35 * time_limit, rng)
            consider(n2, e2)

    if D >= 5:
        # Many short annealing attempts over all semidirect products of a target order.
        rng2 = random.Random(seed * 104729 + d * 31 + D)
        while time.monotonic() < main_deadline:
            k = rng2.choice([1, 1, 2])
            base = best_n // (2 * k)
            span = max(4, base // 4)
            G = base + 1 + rng2.randrange(span)
            groups = _groups_of_order(G, rng2)
            if not groups:
                continue
            order, mul = rng2.choice(groups)
            remaining = main_deadline - time.monotonic()
            slice_end = time.monotonic() + max(1.5, remaining / 6.0)
            attempt_deadline = min(main_deadline, slice_end)
            res = _anneal(d, D, k, order, mul, rng2, attempt_deadline, iters=2500)
            if res is not None:
                consider(res[0], res[1])
    else:
        # Main search for D <= 4: annealed group voltage lifts, with occasional Haar attempts.
        ks = [1, 2, 2, 3, 4]
        haar_m, haar_miss = d + 1, 0
        while time.monotonic() < main_deadline:
            if D <= 4 and haar_miss < 4 and rng.random() < 0.1:
                S = _search_haar(d, D, haar_m, rng, main_deadline, 120)
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
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = None
            groups = _groups_of_order(G, rng)
            if groups:
                g = rng.choice(groups)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, main_deadline, iters=1200)
            if res is not None:
                consider(res[0], res[1])

    # Grow the best graph by pair insertion plus switch-based repair.
    if D >= 3 and best_n >= 2 and time.monotonic() < repair_deadline:
        rng3 = random.Random(seed * 1000003 + d * 17 + D)
        _repair_growth(best_n, list(best[1]), d, D, repair_deadline, rng3, consider)

    # New: twin-shuffle plateau search on the best graph found so far.
    if D >= 3 and best_n >= 2 and time.monotonic() < plateau_deadline:
        rng4 = random.Random(seed * 2654435761 + d * 97 + D)
        _plateau_search(best_n, list(best[1]), d, D, plateau_deadline, rng4, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
