import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane base and arc-extended graphs (diameter 3, record family).
#
# Points are 0..m-1 and lines m..2m-1 in the PG(2, q) incidence graph. For a
# point set S (also read as a line set, same index vectors), add an A-vertex per
# point of S, joined to the q+1 lines through it, and a B-vertex per element of
# S, joined to the q+1 points on that line. Degree load: each line gets one unit
# per S-point on it, each point one unit per S-line through it. So the load
# limit is s = d - q - 1.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points, pts


def _best_pg(d):
    """Plain incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines of S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy S with all loads <= s; returns the largest found."""
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
    """Iterated local search for a large feasible S (all loads <= s), starting from S0."""
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
    """PG incidence plus an A-vertex (2m+t) and a B-vertex (2m+k+t) per element of S."""
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


def _find_arc(q, s, m, pl, lp, pts, rng, deadline):
    """Best feasible arc S found by greedy + conic start + local search, or None."""
    now = time.monotonic()
    starts = [_greedy_arc(m, s, pl, lp, rng, 30, now + 0.3 * max(0.0, deadline - now))]
    if s >= 2:
        index = {p: i for i, p in enumerate(pts)}
        cs = _conic_set(q, index, lib.GF(q))
        if _loads_ok(cs, s, m, pl, lp):
            starts.append(cs)
    S0 = max(starts, key=len)
    if not _loads_ok(S0, s, m, pl, lp):
        S0 = []
    S = _local_arc(m, s, pl, lp, S0, rng, deadline)
    if not S or not _loads_ok(S, s, m, pl, lp):
        return None
    return S


def _arc_phase(d, deadline, rng, base_n):
    """Best arc-extended PG(2, q) graph over prime powers q; None unless it beats base_n."""
    cand = []
    for q in range(2, min(d - 1, 23) + 1):
        s = d - q - 1
        if s < 1 or not lib.is_prime_power(q):
            continue
        m = q * q + q + 1
        kmax = min(m, s * m // (q + 1))  # counting bound: k(q+1) <= s*m
        cand.append((2 * (m + kmax), q, s))
    cand.sort(reverse=True)

    best = None
    best_n = base_n
    for idx, (ub, q, s) in enumerate(cand):
        if ub <= best_n:
            continue
        now = time.monotonic()
        if now >= deadline:
            break
        left = sum(1 for c in cand[idx:] if c[0] > best_n)
        share_end = now + (deadline - now) / max(1, left)
        m, edges, pl, lp, pts = _pg_data(q)
        S = _find_arc(q, s, m, pl, lp, pts, rng, share_end)
        if not S:
            continue
        n, E = _arc_graph(m, edges, pl, lp, S)
        if n > best_n:
            best_n = n
            best = {"n": n, "E": E, "m": m, "edges": edges, "pl": pl, "lp": lp,
                    "S": S, "s": s}
    return best


# ----------------------------------------------------------------------------
# Bold family: start from an over-full arc (one extra point, so some loads
# exceed s), repair degrees, then anneal over edge moves on the whole bipartite
# graph. Cost = (#pairs at distance > D) + 2 * (degree excess).
# ----------------------------------------------------------------------------

def _cost(n, adj, d, D):
    """Bad-pair count at distance > D, plus 2 per unit of degree above d."""
    ball = [0] * n
    for v in range(n):
        x = 1 << v
        for u in adj[v]:
            x |= 1 << u
        ball[v] = x
    for _ in range(D - 1):
        nxt = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt[v] = x
        ball = nxt
    bad2 = 0
    exc = 0
    for v in range(n):
        bad2 += n - ball[v].bit_count()
        dv = len(adj[v]) - d
        if dv > 0:
            exc += dv
    return bad2 // 2 + 2 * exc


def _sa_search(n, color, E0, d, D, deadline, rng):
    """Anneal a bipartite graph (colour 0 / 1) from E0 toward cost 0. Returns (n, edges) or None."""
    adj = [set() for _ in range(n)]
    E = []
    pos = {}

    def add_edge(u, v):
        adj[u].add(v)
        adj[v].add(u)
        pos[(u, v)] = len(E)
        E.append((u, v))

    def rem_edge(u, v):
        adj[u].discard(v)
        adj[v].discard(u)
        i = pos.pop((u, v))
        last = E.pop()
        if i < len(E):
            E[i] = last
            pos[last] = i

    for a, b in E0:
        u, v = (a, b) if color[a] == 0 else (b, a)
        if (u, v) not in pos:
            add_edge(u, v)

    P0 = [v for v in range(n) if color[v] == 0]
    P1 = [v for v in range(n) if color[v] == 1]

    def apply(op):
        if op[0] == 'a':
            add_edge(op[1], op[2])
        else:
            rem_edge(op[1], op[2])

    def undo(op):
        if op[0] == 'a':
            rem_edge(op[1], op[2])
        else:
            add_edge(op[1], op[2])

    # Initial repair: drop random edges at overloaded vertices until degrees fit.
    while True:
        over = [v for v in range(n) if len(adj[v]) > d]
        if not over:
            break
        v = rng.choice(over)
        w = rng.choice(tuple(adj[v]))
        u, x = (v, w) if color[v] == 0 else (w, v)
        rem_edge(u, x)

    cur = _cost(n, adj, d, D)
    start = time.monotonic()
    total = max(1e-3, deadline - start)
    T0, T1 = 1.5, 0.05

    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = T0 * (T1 / T0) ** ((now - start) / total)

        ops = None
        r = rng.random()
        if r < 0.3:
            over = [v for v in range(n) if len(adj[v]) > d]
            if over:
                v = rng.choice(over)
                w = rng.choice(tuple(adj[v]))
                u, x = (v, w) if color[v] == 0 else (w, v)
                ops = [('r', u, x)]
        if ops is None and r < 0.85 and len(E) >= 2:
            a, b = E[rng.randrange(len(E))]
            c, e = E[rng.randrange(len(E))]
            if a != c and b != e and e not in adj[a] and b not in adj[c]:
                ops = [('r', a, b), ('r', c, e), ('a', a, e), ('a', c, b)]
        if ops is None:
            if rng.random() < 0.6:
                u = rng.choice(P0)
                v = rng.choice(P1)
                if v not in adj[u] and len(adj[u]) < d and len(adj[v]) < d:
                    ops = [('a', u, v)]
            elif E:
                a, b = E[rng.randrange(len(E))]
                ops = [('r', a, b)]
        if not ops:
            continue

        for op in ops:
            apply(op)
        new = _cost(n, adj, d, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            for op in reversed(ops):
                undo(op)

    return n, [(u, v) for u, v in E]


def _extra_point(S, m, s, pl, lp, rng):
    """Point outside S whose addition creates the fewest saturated incidences."""
    cl = [0] * m
    cp = [0] * m
    inS = set(S)
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    best_p, best_score = None, None
    for _ in range(60):
        p = rng.randrange(m)
        if p in inS:
            continue
        score = (sum(1 for L in pl[p] if cl[L] >= s)
                 + sum(1 for Q in lp[p] if cp[Q] >= s))
        if best_score is None or score < best_score:
            best_p, best_score = p, score
    return best_p


def _sa_phase(arc, d, D, deadline, rng):
    """Anneal from the best arc plus one extra point. Returns (n, edges) or None."""
    m, edges, pl, lp, S, s = arc["m"], arc["edges"], arc["pl"], arc["lp"], arc["S"], arc["s"]
    p = _extra_point(S, m, s, pl, lp, rng)
    if p is None:
        return None
    S2 = S + [p]
    n, E = _arc_graph(m, edges, pl, lp, S2)
    k2 = len(S2)
    color = [0] * m + [1] * m + [0] * k2 + [1] * k2
    return _sa_search(n, color, E, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d == 2:
        # Even cycle C_{2D}: bipartite, degree 2, diameter D.
        consider(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])
        return best
    if D == 2 or d < 3:
        return best

    # D >= 3: plain projective plane, then the arc family with annealing repair.
    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    arc = _arc_phase(d, start + 0.25 * budget, rng, best_n)
    if arc is not None:
        consider(arc["n"], arc["E"])
        res = _sa_phase(arc, d, D, deadline, rng)
        if res is not None:
            consider(res[0], res[1])

    return best
