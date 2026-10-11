import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions (diameter 3 bipartite).
# ----------------------------------------------------------------------------

def _base_pg(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _conic_points(q):
    """Conic (plus nucleus for even q): an arc in PG(2, q), returned as point indices."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(q, S):
    """PG(2,q) incidence plus one A-vertex per point of S and one B-vertex per line of S.

    Returns (n, edges, side). side[v] = 0 for points and A-vertices, 1 for lines and B-vertices.
    Each edge joins side 0 to side 1, with the side-0 endpoint first.
    """
    n2, pe = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in pe:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    k = len(S)
    n = 2 * m + 2 * k
    E = list(pe)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, P in enumerate(S):  # S is also a set of line indices
        b = 2 * m + k + t
        for Q in line_points[P]:
            E.append((Q, b))
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


# ----------------------------------------------------------------------------
# Bitset ball machinery and cost (number of unordered pairs at distance > D).
# ----------------------------------------------------------------------------

def _ball_r(n, adj, r):
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return ball


def _bad(n, adj, D):
    balls = _ball_r(n, adj, D)
    return sum(n - b.bit_count() for b in balls) // 2


def _add_e(adj, Es, e):
    a, b = e
    adj[a].add(b)
    adj[b].add(a)
    Es.add(e)


def _rem_e(adj, Es, e):
    a, b = e
    adj[a].discard(b)
    adj[b].discard(a)
    Es.discard(e)


# ----------------------------------------------------------------------------
# Repair search: grow by two vertices (one per side), then anneal to diameter 3.
# ----------------------------------------------------------------------------

def _cover_nbrs(n, adj, side, d, want, rng):
    """Greedy choice of up to d deficient opposite-side neighbours for a new vertex on side `want`."""
    ball = _ball_r(n, adj, 2)
    full = (1 << n) - 1
    pool = [v for v in range(n) if side[v] != want and len(adj[v]) < d]
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while pool and len(chosen) < d and covered != full:
        best_g, best_i = -1, -1
        for i, v in enumerate(pool):
            g = (ball[v] & ~covered).bit_count()
            if g > best_g:
                best_g, best_i = g, i
        if best_g <= 0:
            break
        v = pool.pop(best_i)
        chosen.append(v)
        covered |= ball[v]
    return chosen


def _anneal(n, side, E, d, D, deadline, rng):
    """Edge-swap annealing (degree-preserving) plus edge additions between deficient vertices.

    Returns (cost, E). E is a valid edge list only when cost == 0; otherwise it is None.
    """
    E = list(E)
    adj = [set() for _ in range(n)]
    Es = set()
    for a, b in E:
        _add_e(adj, Es, (a, b))
    cost = _bad(n, adj, D)
    if cost == 0:
        return 0, E
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    skips = 0
    while time.monotonic() < deadline:
        if skips > 20000:
            break
        frac = (time.monotonic() - t0) / span
        T = 0.6 * (0.02 / 0.6) ** min(1.0, frac)
        if rng.random() < 0.85 and len(E) >= 2:
            i, j = rng.sample(range(len(E)), 2)
            a, b = E[i]
            c, e = E[j]
            if a == c or b == e:
                skips += 1
                continue
            n1, n2 = (a, e), (c, b)
            if n1 in Es or n2 in Es:
                skips += 1
                continue
            skips = 0
            _rem_e(adj, Es, (a, b))
            _rem_e(adj, Es, (c, e))
            _add_e(adj, Es, n1)
            _add_e(adj, Es, n2)
            E[i], E[j] = n1, n2
            c2 = _bad(n, adj, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                _rem_e(adj, Es, n1)
                _rem_e(adj, Es, n2)
                _add_e(adj, Es, (a, b))
                _add_e(adj, Es, (c, e))
                E[i], E[j] = (a, b), (c, e)
                continue
        else:
            A = [v for v in range(n) if side[v] == 0 and len(adj[v]) < d]
            B = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]
            if not A or not B:
                skips += 1
                continue
            a = rng.choice(A)
            b = rng.choice(B)
            if (a, b) in Es:
                skips += 1
                continue
            skips = 0
            _add_e(adj, Es, (a, b))
            E.append((a, b))
            c2 = _bad(n, adj, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                _rem_e(adj, Es, (a, b))
                E.pop()
                continue
        if cost == 0:
            return 0, E
    return cost, None


def _grow_once(n, E, side, d, D, deadline, rng):
    """Add one side-0 and one side-1 vertex with greedy covers, then anneal. None on failure."""
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    E = list(E)
    side = list(side)
    for want in (0, 1):
        chosen = _cover_nbrs(n, adj, side, d, want, rng)
        v = n
        n += 1
        side.append(want)
        adj.append(set())
        for z in chosen:
            adj[v].add(z)
            adj[z].add(v)
            E.append((v, z) if want == 0 else (z, v))
    cost, E2 = _anneal(n, side, E, d, D, deadline, rng)
    if E2 is None:
        return None
    return n, E2, side


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = 0.85 * time_limit - 1.0 if time_limit > 10 else 0.6 * time_limit
    deadline = start + max(0.5, budget)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    cur = None  # (n, edges, side) of the current valid graph used as repair seed

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        q = _base_pg(d)
        if q is not None:
            n2, pe = lib.projective_plane_incidence(q)
            m = n2 // 2
            side_pg = [0] * m + [1] * m
            if consider(n2, pe):
                cur = (n2, pe, side_pg)
            # Conic-arc extension: needs spare degree >= 2.
            if d - q - 1 >= 2:
                S = _conic_points(q)
                n_a, E_a, side_a = _arc_graph(q, S)
                if consider(n_a, E_a):
                    cur = (n_a, E_a, side_a)

    if D == 3 and cur is not None:
        cur_n, cur_E, cur_side = cur
        while time.monotonic() < deadline:
            res = _grow_once(cur_n, cur_E, cur_side, d, D, deadline, rng)
            if res is None:
                break
            n2, E2, side2 = res
            if not consider(n2, E2):
                break
            cur_n, cur_E, cur_side = n2, E2, side2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
