import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane base and arc extensions (diameter 3, as in the parent).
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
    """Randomized greedy arc with all loads <= s; returns the largest found."""
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


def _arc_extensions(d, deadline, rng, threshold):
    """Return (n, edges) candidates from arc-extended projective planes."""
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
# Graph utilities on adjacency sets.
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _edges_from_adj(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _bipartition(n, adj):
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


def _bad_count(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs count). Zero means valid."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _apply(adj, rem, add):
    for u, v in rem:
        adj[u].discard(v)
        adj[v].discard(u)
    for u, v in add:
        adj[u].add(v)
        adj[v].add(u)


# ----------------------------------------------------------------------------
# New family: growth by two vertices with annealed repair at fixed order.
#
# From a valid graph on n vertices we add one A-vertex and one B-vertex, fill
# spare degree greedily, then anneal over degree-preserving 2-switches and
# edge-insertion moves that absorb the remaining deficiency. Cost is the number
# of bad pairs; zero means diameter <= D.
# ----------------------------------------------------------------------------

def _fill(n, adj, color, d, rng):
    """Greedily add edges between deficient opposite-side vertices (monotone: never hurts)."""
    A = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    B = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    rng.shuffle(A)
    rng.shuffle(B)
    for a in A:
        if len(adj[a]) >= d:
            continue
        for b in B:
            if len(adj[b]) < d and b not in adj[a]:
                adj[a].add(b)
                adj[b].add(a)
                if len(adj[a]) >= d:
                    break


def _move_switch(adj, Avs, rng):
    a1 = rng.choice(Avs)
    a2 = rng.choice(Avs)
    if a1 == a2 or not adj[a1] or not adj[a2]:
        return None
    b1 = rng.choice(tuple(adj[a1]))
    b2 = rng.choice(tuple(adj[a2]))
    if b2 in adj[a1] or b1 in adj[a2]:
        return None
    return [(a1, b1), (a2, b2)], [(a1, b2), (a2, b1)]


def _move_insert(adj, Avs, Bvs, d, rng):
    defA = [a for a in Avs if len(adj[a]) < d]
    defB = [b for b in Bvs if len(adj[b]) < d]
    if not defA or not defB:
        return None
    a = rng.choice(defA)
    b = rng.choice(defB)
    if b in adj[a]:
        return None
    a2 = rng.choice(Avs)
    if a2 == a or not adj[a2]:
        return None
    b2 = rng.choice(tuple(adj[a2]))
    if b2 in adj[a] or b in adj[a2]:
        return None
    return [(a2, b2)], [(a, b2), (a2, b)]


def _anneal(n, adj, color, d, D, rng, deadline, cost):
    """Simulated annealing on bad-pair count at fixed order. Returns final cost."""
    Avs = [v for v in range(n) if color[v] == 0]
    Bvs = [v for v in range(n) if color[v] == 1]
    if not Avs or not Bvs:
        return cost
    t0 = time.monotonic()
    span = max(deadline - t0, 1e-3)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = 0.5 * (0.01 ** frac)
        if rng.random() < 0.3:
            mv = _move_insert(adj, Avs, Bvs, d, rng)
        else:
            mv = _move_switch(adj, Avs, rng)
        if mv is None:
            continue
        rem, add = mv
        _apply(adj, rem, add)
        c2 = _bad_count(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _apply(adj, add, rem)
    return cost


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    bound = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
    if best_n >= bound:
        return best_n, best_e

    arc_deadline = start + 0.4 * budget
    for n_c, e_c in _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d), best_n):
        consider(n_c, e_c)
    if best_n >= bound:
        return best_n, best_e

    # Growth with annealed repair from the best valid graph found so far.
    rng = random.Random(seed * 31 + 7)
    cur_n = best_n
    cur_adj = _adjacency(best_n, best_e)
    cur_color = _bipartition(best_n, cur_adj)

    while time.monotonic() < deadline and cur_n + 2 <= bound:
        n2 = cur_n + 2
        adj2 = [set(s) for s in cur_adj] + [set(), set()]
        color2 = cur_color + [0, 1]
        _fill(n2, adj2, color2, d, rng)
        cost = _bad_count(n2, adj2, D)
        now = time.monotonic()
        step_deadline = now + max(0.5, 0.6 * (deadline - now))
        cost = _anneal(n2, adj2, color2, d, D, rng, step_deadline, cost)
        if cost == 0:
            e2 = _edges_from_adj(n2, adj2)
            if lib.is_valid(n2, e2, d, D):
                consider(n2, e2)
                cur_n, cur_adj, cur_color = n2, adj2, color2

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
