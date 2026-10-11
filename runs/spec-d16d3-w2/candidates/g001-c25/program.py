import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base and arc-extended incidence graphs (diameter 3).
#
# PG(2, q) incidence with spare degree s = d - q - 1 on every vertex. Choose a
# point set S with every line holding <= s points of S and every point on <= s
# lines of S. Add an A-vertex per point of S (joined to its q+1 lines) and a
# B-vertex per line of S (joined to its q+1 points).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _local_arc(m, s, point_lines, line_points, S0, rng, deadline):
    """Iterated local search for a large feasible S, starting from S0."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m
    S = []

    def add(P):
        inS[P] = True
        S.append(P)
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def remove(P):
        inS[P] = False
        S.remove(P)
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def blockers(P):
        satL = {L for L in point_lines[P] if cl[L] >= s}
        satQ = {Q for Q in line_points[P] if cp[Q] >= s}
        if not satL and not satQ:
            return []
        return [R for R in S
                if any(L in satL for L in point_lines[R])
                or any(Q in satQ for Q in line_points[R])]

    for P in S0:
        add(P)
    best = list(S)
    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        B = blockers(P)
        if not B:
            add(P)
        elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.1):
            for R in B:
                remove(R)
            add(P)
        else:
            continue
        if len(S) > len(best):
            best = list(S)
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A (point side) and a new B (line side) vertex per element of S."""
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


def _arc_extensions(d, deadline, rng, threshold):
    """Return (n, edges) candidates from arc-extended PG(2, q) for prime powers q with q + 1 <= d."""
    qs = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1:
            continue
        m = q * q + q + 1
        kmax = s * m // (q + 1)
        if 2 * m + 2 * kmax <= threshold:
            continue
        qs.append((q, s))

    out = []
    for idx, (q, s) in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        q_deadline = now + share
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, now + 0.3 * share)]
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S0 = max(cands, key=len, default=[])
        if not _loads_ok(S0, s, m, point_lines, line_points):
            S0 = []
        S = _local_arc(m, s, point_lines, line_points, S0, rng, q_deadline)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Repair-grow: insert one vertex at a time, then anneal the graph back to
# diameter <= D by degree-preserving double edge swaps (bipartiteness and
# degree bounds are preserved by construction). Cost = number of ordered
# vertex pairs at distance > D (unreachable counted too).
# ----------------------------------------------------------------------------

def _cost_of(n, adj, D):
    """Number of ordered pairs at distance > D (0 means diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt[v] = r
        reach = nxt
    return sum(n - r.bit_count() for r in reach)


def _repair_grow(n, edges, d, D, deadline, rng):
    """Repeatedly add a vertex joined to spare-capacity vertices, then repair by swaps."""
    adj0 = [set() for _ in range(n)]
    for u, v in edges:
        adj0[u].add(v)
        adj0[v].add(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj0[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    E0 = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]

    cur_n, cur_col, cur_E, cur_adj = n, color, E0, adj0
    best = (n, list(edges))
    ITER = 700
    T0, T1 = 2.0, 0.05

    while time.monotonic() < deadline:
        sides = [0, 1]
        rng.shuffle(sides)
        c = None
        opp = []
        for cc in sides:
            opp = [x for x in range(cur_n) if cur_col[x] != cc and len(cur_adj[x]) < d]
            if len(opp) >= 2:
                c = cc
                break
        if c is None:
            break

        k = min(d, len(opp))
        nb = rng.sample(opp, k)
        N = cur_n
        col = cur_col + [c]
        adj = [set(s) for s in cur_adj] + [set(nb)]
        for x in nb:
            adj[x].add(N)
        E2 = list(cur_E) + [((N, x) if c == 0 else (x, N)) for x in nb]

        cost = _cost_of(N + 1, adj, D)
        it = 0
        while cost > 0 and it < ITER and time.monotonic() < deadline:
            it += 1
            T = T0 * (T1 / T0) ** (it / ITER)
            m = len(E2)
            i = rng.randrange(m)
            j = rng.randrange(m)
            if i == j:
                continue
            a, b = E2[i]
            p, q2 = E2[j]
            # a, p on side 0; b, q2 on side 1. Swap to (a, q2), (p, b).
            if a == p or b == q2 or q2 in adj[a] or b in adj[p]:
                continue
            adj[a].discard(b)
            adj[b].discard(a)
            adj[p].discard(q2)
            adj[q2].discard(p)
            adj[a].add(q2)
            adj[q2].add(a)
            adj[p].add(b)
            adj[b].add(p)
            new_cost = _cost_of(N + 1, adj, D)
            delta = new_cost - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = new_cost
                E2[i] = (a, q2)
                E2[j] = (p, b)
            else:
                adj[a].discard(q2)
                adj[q2].discard(a)
                adj[p].discard(b)
                adj[b].discard(p)
                adj[a].add(b)
                adj[b].add(a)
                adj[p].add(q2)
                adj[q2].add(p)

        if cost == 0:
            e_list = [(min(a, b), max(a, b)) for a, b in E2]
            if lib.is_valid(N + 1, e_list, d, D):
                cur_n, cur_col, cur_E, cur_adj = N + 1, col, E2, adj
                best = (N + 1, e_list)
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = 0.8 * time_limit
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
            for n_c, e_c in _arc_extensions(d, start + 0.35 * budget,
                                            random.Random(seed * 7919 + d), best[0]):
                consider(n_c, e_c)

        if D >= 2 and time.monotonic() < deadline:
            n2, e2 = _repair_grow(best[0], best[1], d, D, deadline, rng)
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
