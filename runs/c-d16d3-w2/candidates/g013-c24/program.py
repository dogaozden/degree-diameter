import math
import random
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3). Kept from the
# parent as base constructions.
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
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, S, line_points):
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
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, S, line_points))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4), kept from the parent.
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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction: cover-growth by simulated annealing.
#
# Adding a new vertex x on one side, joined to a set T on the opposite side
# (every member of T having spare degree), can never lengthen any existing
# shortest path, so the whole graph stays within diameter D exactly when x
# reaches every other vertex within D steps. So the only thing to check is
# the BFS ball of x, and we search over T with annealing to maximise that ball.
# Each accepted vertex is a new point of growth; new vertices also become
# eligible neighbours later, so the graph grows beyond the algebraic bases.
# ----------------------------------------------------------------------------

def _adj_from(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _colour(n, adj):
    """Proper 2-colouring, or None if the graph is not bipartite."""
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
                elif col[v] == col[u]:
                    return None
    return col


def _edges_of(adj):
    return [(u, v) for u, nb in enumerate(adj) for v in nb if u < v]


def _reach(adj, T, D):
    """Number of vertices within distance D of a new vertex x joined to T (x counted)."""
    n = len(adj)
    seen = bytearray(n)
    frontier = []
    for t in T:
        if not seen[t]:
            seen[t] = 1
            frontier.append(t)
    count = 1 + len(frontier)
    for _ in range(D - 1):
        if not frontier:
            break
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = 1
                    nxt.append(v)
        count += len(nxt)
        frontier = nxt
    return count


def _pick_out(elig, S, rng):
    """A random eligible vertex not in S, or None."""
    for _ in range(30):
        c = elig[rng.randrange(len(elig))]
        if c not in S:
            return c
    return None


def _cover_sa(adj, color, d, D, tcol, rng, iters, deadline):
    """Anneal a neighbourhood T (colour tcol, spare degree, |T| <= d) so a new vertex reaches all."""
    n = len(adj)
    elig = [v for v in range(n) if color[v] == tcol and len(adj[v]) < d]
    if not elig:
        return None
    cap = min(d, len(elig))
    T = rng.sample(elig, cap)
    cost = (n + 1) - _reach(adj, T, D)
    temp = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.03, temp * 0.99)
        S = set(T)
        newT = list(T)
        r = rng.random()
        if r < 0.3 and len(newT) < cap:
            c = _pick_out(elig, S, rng)
            if c is None:
                continue
            newT.append(c)
        elif r < 0.45 and len(newT) > 1:
            newT.pop(rng.randrange(len(newT)))
        else:
            c = _pick_out(elig, S, rng)
            if c is None:
                continue
            newT[rng.randrange(len(newT))] = c
        c2 = (n + 1) - _reach(adj, newT, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            T = newT
            cost = c2
    return T if cost == 0 else None


def _grow(adj, color, d, D, rng, deadline, fail_limit, iters):
    """Repeatedly add cover-vertices until several consecutive attempts fail or time runs out."""
    adj = [list(a) for a in adj]
    color = list(color)
    fails = 0
    while fails < fail_limit and time.monotonic() < deadline:
        tcol = rng.randrange(2)
        T = _cover_sa(adj, color, d, D, tcol, rng, iters, deadline)
        if T is None:
            fails += 1
            continue
        x = len(adj)
        adj.append(list(T))
        for t in T:
            adj[t].append(x)
        color.append(1 - tcol)
        fails = 0
    return adj, color


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    cands = [fallback]
    if D >= 3:
        base_end = start + 0.3 * time_limit
        cands.extend(_arc_extensions(d, base_end, random.Random(seed * 7919 + d)))
        # Plain projective plane for the largest prime power q with q + 1 <= d.
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                cands.append(lib.projective_plane_incidence(q))
                break
        # Araujo-Pardo / Lopez record when d - 2 is a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            cands.append(gq)

    valid = []
    for n_c, e_c in cands:
        if lib.is_valid(n_c, e_c, d, D):
            valid.append((n_c, e_c))
    valid.sort(key=lambda t: -t[0])
    if not valid:
        return fallback

    best_n, best_E = valid[0]
    # Grow the two largest distinct bases, sharing the remaining time.
    targets = valid[:2]
    for i, (n_c, e_c) in enumerate(targets):
        now = time.monotonic()
        remaining = end - now
        if remaining <= 0:
            break
        share = remaining / (len(targets) - i)
        adj = _adj_from(n_c, e_c)
        col = _colour(n_c, adj)
        if col is None:
            continue
        adj2, _ = _grow(adj, col, d, D, random.Random(seed * 31 + i), now + share, 12, 150)
        n2 = len(adj2)
        if n2 > best_n:
            E2 = _edges_of(adj2)
            if lib.is_valid(n2, E2, d, D):
                best_n, best_E = n2, E2

    if not lib.is_valid(best_n, best_E, d, D):
        return fallback
    return best_n, best_E
