import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base and arc-extended graphs (diameter 3).
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
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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


def _arc_candidates(d, rng, deadline):
    """Arc-extended PG graphs (conic and greedy arcs) for prime powers q with spare degree."""
    out = []
    qs = [q for q in range(2, min(d - 1, 23) + 1)
          if lib.is_prime_power(q) and d - q - 1 >= 1]
    for q in qs:
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        cs = _conic_set(q, index, lib.GF(q))
        if _loads_ok(cs, s, m, point_lines, line_points):
            cands.append(cs)
        g = _greedy_arc(m, s, point_lines, line_points, rng, 30,
                        min(deadline, time.monotonic() + 1.0))
        if g and _loads_ok(g, s, m, point_lines, line_points):
            cands.append(g)
        for S in cands:
            if S:
                out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Bold search: insert a vertex, then anneal degree-preserving double-edge swaps
# until the diameter condition holds again (cost = number of bad pairs).
# ----------------------------------------------------------------------------

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


def _saturate(n, E, color, d, rng):
    """Add edges between deficient opposite-side vertices in random order (E normalized as (side0, side1))."""
    deg = [0] * n
    keys = set()
    for a, b in E:
        deg[a] += 1
        deg[b] += 1
        keys.add((a, b))
    L = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    R = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in L for b in R if (a, b) not in keys]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            E.append((a, b))
            keys.add((a, b))
            deg[a] += 1
            deg[b] += 1
    return E


def _anneal(n, edges, color, d, D, deadline, rng):
    """Anneal double-edge swaps (degree and bipartition preserved) until diameter <= D; None on failure."""
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    E = _saturate(n, E, color, d, rng)
    if len(E) < 2:
        return None
    cost = lib.bad_pairs(n, E, D)
    if cost == 0:
        return E
    keys = set(E)
    m = len(E)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        T = 1.5 * (0.05 ** frac)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        a2, b2 = E[j]
        if a == a2 or b == b2:
            continue
        e1 = (a, b2)
        e2 = (a2, b)
        if e1 in keys or e2 in keys:
            continue
        E[i] = e1
        E[j] = e2
        keys.discard((a, b))
        keys.discard((a2, b2))
        keys.add(e1)
        keys.add(e2)
        c2 = lib.bad_pairs(n, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost == 0:
                return E
        else:
            E[i] = (a, b)
            E[j] = (a2, b2)
            keys.discard(e1)
            keys.discard(e2)
            keys.add((a, b))
            keys.add((a2, b2))
    return None


def _grow(n, edges, d, D, deadline, rng):
    """Repeatedly insert a vertex and anneal to restore diameter D; returns the largest valid graph reached."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        adj = [[] for _ in range(cur_n)]
        for u, v in cur_e:
            adj[u].append(v)
            adj[v].append(u)
        color = _bipartition(cur_n, adj)
        deg = [len(a) for a in adj]
        c = rng.randrange(2)
        cands = [v for v in range(cur_n) if color[v] == 1 - c and deg[v] < d]
        if not cands:
            c = 1 - c
            cands = [v for v in range(cur_n) if color[v] == 1 - c and deg[v] < d]
        if not cands:
            break
        rng.shuffle(cands)
        v_new = cur_n
        trial_e = list(cur_e) + [(x, v_new) for x in cands[:d]]
        trial_color = color + [c]
        now = time.monotonic()
        budget = max(1.0, 0.5 * (deadline - now))
        res = _anneal(cur_n + 1, trial_e, trial_color, d, D, now + budget, rng)
        if res is not None:
            cur_n += 1
            cur_e = res
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Driver with safe fallback.
# ----------------------------------------------------------------------------

def _fallback(d, D):
    """Always-valid fallback: K_{d,d} (diameter 2) or a single edge."""
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


def _main(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    best = _fallback(d, D)
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        for n_c, e_c in _arc_candidates(d, rng, start + 0.25 * time_limit):
            consider(n_c, e_c)
        n2, e2 = _grow(best[0], best[1], d, D, deadline, rng)
        consider(n2, e2)

    return best


def build(d, D, seed, time_limit):
    try:
        n, e = _main(d, D, seed, time_limit)
        if lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return _fallback(d, D)
