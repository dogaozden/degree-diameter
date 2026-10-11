import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane bases and the Araujo-Lopez record graph (D = 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph (degree q+2) when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, AssertionError):
        return None


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
# Spare capacity s = d - q - 1; pick points S with every line and point loaded
# at most s, then add an A-vertex and a B-vertex per element of S.
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
# NEW: pair insertion with 2-switch repair.
#
# State: (n, adj, E) where adj[v] is a set of neighbours and E is a list of
# [a, b] edges with a on side A (colour 0) and b on side B (colour 1).
#
# Insert a new A-vertex x and B-vertex y: choose d-1 edges with pairwise
# distinct endpoints, rewire each a-b to x-b and a-y, then add x-y. Every old
# degree is preserved, x and y reach degree d, and bipartiteness is kept.
#
# Repair: simulated annealing over 2-switches (a1-b1, a2-b2 -> a1-b2, a2-b1).
# 2-switches preserve all degrees and bipartiteness. The cost is the number of
# vertex pairs at distance > D. Cost 0 gives a valid graph by construction.
# ----------------------------------------------------------------------------

def _bipartition(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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


def _make_state(n, edges):
    color = _bipartition(n, edges)
    adj = [set() for _ in range(n)]
    E = []
    for u, v in edges:
        a, b = (u, v) if color[u] == 0 else (v, u)
        E.append([a, b])
        adj[a].add(b)
        adj[b].add(a)
    return n, adj, E


def _copy_state(st):
    n, adj, E = st
    return n, [set(s) for s in adj], [list(e) for e in E]


def _bad(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs count)."""
    reach = [1 << v for v in range(n)]
    nb = [tuple(s) for s in adj]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _retarget(st, i, j, new_i, new_j):
    """Replace edges E[i], E[j] by new_i, new_j, keeping adjacency consistent."""
    _, adj, E = st
    for a, b in (E[i], E[j]):
        adj[a].discard(b)
        adj[b].discard(a)
    E[i] = new_i
    E[j] = new_j
    for a, b in (new_i, new_j):
        adj[a].add(b)
        adj[b].add(a)


def _insert_pair(st, d, rng):
    """Return a new state with one extra A-vertex and one extra B-vertex, or None."""
    n, adj, E = st
    order = list(range(len(E)))
    rng.shuffle(order)
    used_a, used_b, chosen = set(), set(), []
    for idx in order:
        a, b = E[idx]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        chosen.append(idx)
        if len(chosen) == d - 1:
            break
    if len(chosen) < d - 1:
        return None
    x, y = n, n + 1
    cand = (n + 2, adj + [set(), set()], E)
    for idx in chosen:
        a, b = E[idx]
        _retarget(cand, idx, idx, [x, b], [x, b])  # placeholder, fixed below
        # Undo the placeholder effect precisely and apply the true rewiring.
        adj[a].add(b)
        adj[b].add(a)
    return None if False else _finish_insert(cand, n, chosen, d)


def _finish_insert(cand, n, chosen, d):
    """Apply the rewiring for the chosen edges (helper for _insert_pair)."""
    n2, adj, E = cand
    x, y = n, n + 1
    # Recompute from a clean copy to avoid any placeholder side effects.
    return None


def _insert_clean(st, d, rng):
    """Clean implementation of pair insertion."""
    n, adj0, E0 = st
    order = list(range(len(E0)))
    rng.shuffle(order)
    used_a, used_b, chosen = set(), set(), []
    for idx in order:
        a, b = E0[idx]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        chosen.append(idx)
        if len(chosen) == d - 1:
            break
    if len(chosen) < d - 1:
        return None
    x, y = n, n + 1
    adj = [set(s) for s in adj0] + [set(), set()]
    E = [list(e) for e in E0]
    for idx in chosen:
        a, b = E[idx]
        adj[a].discard(b)
        adj[b].discard(a)
        E[idx] = [x, b]
        adj[x].add(b)
        adj[b].add(x)
        E.append([a, y])
        adj[a].add(y)
        adj[y].add(a)
    E.append([x, y])
    adj[x].add(y)
    adj[y].add(x)
    return n + 2, adj, E


def _repair(st, D, rng, deadline, iters):
    """Anneal 2-switches until the cost (bad pairs) is zero. Returns True on success."""
    n, adj, E = st
    if len(E) < 2:
        return False
    cost = _bad(n, adj, D)
    T0, T1 = 1.0, 0.05
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue
        old1, old2 = E[i], E[j]
        _retarget(st, i, j, [a1, b2], [a2, b1])
        c2 = _bad(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _retarget(st, i, j, old1, old2)
    return cost == 0


def _grow_insert(n0, edges, d, D, deadline, rng):
    """Repeatedly insert a vertex pair and repair. Returns the list of valid (n, edges) found."""
    st = _make_state(n0, edges)
    results = []
    while time.monotonic() < deadline:
        ok = False
        for _ in range(6):
            if time.monotonic() >= deadline:
                break
            cand = _insert_clean(_copy_state(st), d, rng)
            if cand is None:
                break
            if _repair(cand, D, rng, deadline, 2000):
                st = cand
                ok = True
                break
        if not ok:
            break
        n, _, E = st
        results.append((n, [(a, b) for a, b in E]))
    return results


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        rec = _araujo(d)
        if rec is not None:
            consider(rec[0], rec[1])
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        for n_c, e_c in _arc_extensions(d, start + 0.2 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    # New phase: grow the best base by pair insertion with 2-switch repair.
    results = _grow_insert(best[0], list(best[1]), d, D, deadline, rng)
    if results:
        consider(*results[-1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
