import math
import random
import time

import lib

_BIG = 10 ** 9
_D = 3


def _largest_pp_at_most(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _smallest_pp_at_least(x):
    q = max(2, x)
    while not lib.is_prime_power(q):
        q += 1
    return q


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3, baseline family).
# ----------------------------------------------------------------------------

def _pg_data(q):
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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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


def _local_improve(m, s, point_lines, line_points, S, rng, deadline, iters):
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m

    def add(P):
        inS[P] = True
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def rem(P):
        inS[P] = False
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def fits(P):
        return (all(cl[L] < s for L in point_lines[P])
                and all(cp[Q] < s for Q in line_points[P]))

    cur = list(S)
    for P in cur:
        add(P)
    best = list(cur)
    for it in range(iters):
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        if fits(P):
            add(P)
            cur.append(P)
            if len(cur) > len(best):
                best = list(cur)
            continue
        if not cur:
            continue
        idx = rng.randrange(len(cur))
        R = cur[idx]
        rem(R)
        if fits(P):
            add(P)
            cur[idx] = P
        else:
            add(R)
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
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
            g = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
            g = _local_improve(m, s, point_lines, line_points, g, rng, deadline, 3000)
            cands.append(g)
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
# New family (D = 3): anneal over deletions from PG(2, q), q >= d.
#
# PG(2,q) has degree q+1 > d, so each side must lose vertices. We choose a
# set of dead points and dead lines. The state is the alive mask. Cost is the
# number of alive pairs at distance > 3, plus a penalty for alive vertices of
# degree > d. We alternate between shrinking the deleted set (when cost is 0)
# and growing it (when annealing stalls), always keeping the best valid induced
# subgraph seen.
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _cost(n, adj, alive, d):
    nb = [[] for _ in range(n)]
    excess = 0
    live = []
    for v in range(n):
        if alive[v]:
            live.append(v)
            nbv = [u for u in adj[v] if alive[u]]
            nb[v] = nbv
            if len(nbv) > d:
                excess += len(nbv) - d
    nlive = len(live)
    if nlive == 0:
        return _BIG
    reach = [0] * n
    for v in live:
        reach[v] = 1 << v
    for _ in range(_D):
        new = [0] * n
        for v in live:
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    bad = sum(nlive - reach[v].bit_count() for v in live) // 2
    return bad + 5 * excess


def _induced(n, edges, alive):
    idx = {}
    for v in range(n):
        if alive[v]:
            idx[v] = len(idx)
    E = [(idx[u], idx[v]) for u, v in edges if alive[u] and alive[v]]
    return len(idx), E


def _deletion_search(d, n, edges, deadline, rng, consider):
    m = n // 2
    adj = _adjacency(n, edges)
    alive = [True] * n
    t = int(0.4 * m)

    def pick(side, want_alive):
        off = side * m
        while True:
            v = off + rng.randrange(m)
            if alive[v] == want_alive:
                return v

    for _ in range(t):
        for side in (0, 1):
            alive[pick(side, True)] = False

    cur = _cost(n, adj, alive, d)
    K = 300
    while time.monotonic() < deadline:
        steps = 0
        while cur > 0 and steps < K and t > 0 and time.monotonic() < deadline:
            steps += 1
            T = 0.1 ** (steps / K)
            side = rng.randrange(2)
            a = pick(side, True)
            b = pick(side, False)
            alive[a] = False
            alive[b] = True
            c2 = _cost(n, adj, alive, d)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c2
            else:
                alive[a] = True
                alive[b] = False

        if cur == 0:
            cn, ce = _induced(n, edges, alive)
            consider(cn, ce)
            if t <= 0:
                break
            for side in (0, 1):
                alive[pick(side, False)] = True
            t -= 1
        else:
            if t + 2 >= m - 1:
                break
            for side in (0, 1):
                for _ in range(2):
                    alive[pick(side, True)] = False
            t += 2
        cur = _cost(n, adj, alive, d)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    # Plain PG(2,q) incidence, q the largest prime power with q+1 <= d.
    q0 = _largest_pp_at_most(d - 1)
    if q0 is not None:
        n0, e0 = lib.projective_plane_incidence(q0)
        consider(n0, e0)

    if best[0] >= lib.moore_bound(d, _D):
        return best

    # Baseline family: arc-extended projective plane graphs.
    for n_c, e_c in _arc_extensions(d, start + 0.25 * time_limit,
                                    random.Random(seed * 7919 + d)):
        consider(n_c, e_c)

    # New family: deletion annealing from PG(2, q) with q >= d.
    q1 = _smallest_pp_at_least(d)
    if q1 <= 25:
        n1, e1 = lib.projective_plane_incidence(q1)
        _deletion_search(d, n1, e1, start + 0.88 * time_limit,
                         random.Random(seed * 104729 + d), consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
