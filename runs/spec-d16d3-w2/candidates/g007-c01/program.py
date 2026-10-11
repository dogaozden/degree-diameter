"""Arc-extended projective plane construction for bipartite diameter-3 graphs.

Base: the incidence graph of PG(2, q), with q the largest prime power below d.
Spare degree s = d - q - 1 on every base vertex is spent on two independent
packings. S (points) gets an A-vertex joined to the q+1 lines through each point
of S. T (lines) gets a B-vertex joined to the q+1 points on each line of T.
Each packing keeps every line (resp. point) below s uses. Diameter stays 3 and
the graph stays bipartite for any such S and T.

New here relative to the parent: S and T are searched independently (the parent
coupled them), both are seeded with the conic, and a counting bound
(|S|, |T| <= s*m/(q+1)) prunes candidate q values before any search time is spent.

Honest scope: for d=16, q=13, s=2, a set with at most 2 points per line is a
2-arc, so |S| <= q+1 = 14 and |T| <= 14. This family therefore tops out at
2*183 + 28 = 394, which equals the record and does not beat it.
"""
import random
import time

import lib


def _pg_structure(q):
    """Return (m, edges, point_lines, line_points) for the incidence graph of PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _conic_indices(q):
    """Conic (plus nucleus for even q) as point indices in PG(2, q). Usable as point or line sets."""
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _packing(m, cover, s, rng, deadline, init, target):
    """Largest X (subset of 0..m-1) so every resource is covered at most s times by X.

    cover[i] lists the resources touched by item i. Items are added when free.
    Otherwise the blocking items are removed (1 or 2 of them, with a plateau move
    on single blockers). After a long stall, two random items are dropped.
    Stops at `deadline` or once |X| reaches `target`.
    """
    load = [0] * m
    inX = [False] * m
    X = []

    def add(i):
        inX[i] = True
        X.append(i)
        for r in cover[i]:
            load[r] += 1

    def remove(i):
        inX[i] = False
        X.remove(i)
        for r in cover[i]:
            load[r] -= 1

    def blockers(i):
        sat = {r for r in cover[i] if load[r] >= s}
        if not sat:
            return []
        return [j for j in X if any(r in sat for r in cover[j])]

    for i in init:
        if not inX[i] and not blockers(i):
            add(i)

    best = list(X)
    stall = 0
    while time.monotonic() < deadline and len(best) < target:
        i = rng.randrange(m)
        if inX[i]:
            stall += 1
            continue
        B = blockers(i)
        if not B:
            add(i)
        elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.15):
            for j in B:
                remove(j)
            add(i)
        else:
            stall += 1
        if len(X) > len(best):
            best = list(X)
            stall = 0
        if stall > 4000 and len(X) >= 2:
            for j in rng.sample(X, 2):
                remove(j)
            stall = 0
    return best


def _arc_graph(q, s, rng, t_s, t_t, target):
    """Build PG(2,q) + A-vertices for packing S + B-vertices for packing T."""
    m, edges, point_lines, line_points = _pg_structure(q)
    init = _conic_indices(q) if (s >= 1 and q >= 3) else []
    S = _packing(m, point_lines, s, rng, t_s, init, target)
    T = _packing(m, line_points, s, rng, t_t, init, target)
    n = 2 * m + len(S) + len(T)
    E = list(edges)
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in point_lines[P]:
            E.append((a, m + L))
    base_b = 2 * m + len(S)
    for t, L in enumerate(T):
        b = base_b + t
        for Q in line_points[L]:
            E.append((Q, b))
    return n, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = list(lib.haar_graph(d, range(d)))

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    if D >= 3:
        qs = sorted((q for q in range(2, d) if lib.is_prime_power(q)), reverse=True)
        if qs:
            consider(*lib.projective_plane_incidence(qs[0]))

        # Counting-bound pruning: |S|, |T| <= s*m/(q+1) since each center uses q+1 slots.
        cands = []
        for q in qs:
            s = d - q - 1
            if s < 1 or q < 3:
                continue
            m = q * q + q + 1
            kmax = s * m // (q + 1)
            if 2 * m + 2 * kmax <= best[0]:
                continue
            cands.append((q, s, kmax))

        for idx, (q, s, kmax) in enumerate(cands):
            now = time.monotonic()
            if now >= deadline:
                break
            share = (deadline - now) / (len(cands) - idx)
            t_s = now + 0.5 * share
            t_t = now + share
            n_c, e_c = _arc_graph(q, s, rng, t_s, t_t, kmax)
            consider(n_c, e_c)

    n, e = best
    if not lib.is_valid(n, e, d, D):
        n, e = lib.haar_graph(d, range(d))
    return n, e
