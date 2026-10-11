"""Twin blow-up of projective planes with independent load-constrained sets (D = 3).

View PG(2, q) as a bipartite incidence graph (points 0..m-1, lines m..2m-1).
Adding a twin A-vertex for a point P (adjacent to the lines through P) or a
twin B-vertex for a line j (adjacent to the points on j) keeps diameter 3:
- twin-to-twin and point-to-point distances are 2 through a common line;
- an A-vertex for P reaches every point within 2 (via the line through P and that point);
- A-to-B distance is 3 (A_P - L - Q - B_j, with L = PQ and Q on j).
So the only constraint is degree. A line may gain at most s = d - (q+1) A-twins,
which means the chosen point set X meets every line in at most s points. A point
may gain at most s B-twins, which means the chosen line set Y has at most s lines
through each point. X and Y are chosen independently by a swap-based local search
seeded with a conic (an arc). The graph is then checked with lib.is_valid.
"""
import random
import time

import lib


def _incidence_lists(m, edges):
    """Return (point_lines, line_points) for PG(2,q) with points 0..m-1 and lines m..2m-1."""
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return pl, lp


def _conic_init(q, idx):
    """Conic (plus nucleus for even q) as a list of point indices: an arc with no three collinear."""
    F = lib.GF(q)
    S = [idx[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(idx[(0, 0, 1)])
    if q % 2 == 0:
        S.append(idx[(0, 1, 0)])
    return S


def _max_load_set(C, ncons, s, rng, deadline, init=()):
    """Large set of elements with every constraint used at most s times.

    C[e] lists the constraints containing element e (ncons constraints in total).
    Local search: add free elements, and swap an element in when its blockers can
    be removed. Starts from `init` (kept only where feasible), then random order.
    Returns the best chosen element list found.
    """
    m = len(C)
    if s <= 0 or m == 0:
        return []
    members = [[] for _ in range(ncons)]
    for e in range(m):
        for c in C[e]:
            members[c].append(e)
    Cset = [frozenset(c) for c in C]
    chosen = [False] * m
    cnt = [0] * ncons
    size = 0

    def add(e):
        nonlocal size
        chosen[e] = True
        size += 1
        for c in C[e]:
            cnt[c] += 1

    def drop(e):
        nonlocal size
        chosen[e] = False
        size -= 1
        for c in C[e]:
            cnt[c] -= 1

    order = list(range(m))
    rng.shuffle(order)
    for e in list(init) + order:
        if not chosen[e] and all(cnt[c] < s for c in C[e]):
            add(e)
    best = [e for e in range(m) if chosen[e]]

    it = 0
    while True:
        it += 1
        if (it & 511) == 0 and time.monotonic() > deadline:
            break
        e = rng.randrange(m)
        if chosen[e]:
            continue
        full = [c for c in C[e] if cnt[c] >= s]
        if not full:
            add(e)
        else:
            c = rng.choice(full)
            f = rng.choice([x for x in members[c] if chosen[x]])
            if all(cnt[k] - (1 if k in Cset[f] else 0) < s for k in C[e]):
                drop(f)
                add(e)
            else:
                continue
        if size > len(best):
            best = [x for x in range(m) if chosen[x]]
    return best


def _twin_graph(m, edges, pl, lp, X, Y):
    """PG(2,q) incidence plus A-twins for points X and B-twins for lines Y."""
    nX, nY = len(X), len(Y)
    n = 2 * m + nX + nY
    E = list(edges)
    for t, P in enumerate(X):
        a = 2 * m + t
        for L in pl[P]:
            E.append((a, m + L))
    for t, j in enumerate(Y):
        b = 2 * m + nX + t
        for Q in lp[j]:
            E.append((Q, b))
    return n, E


def _best_twin_graph(q, d, rng, deadline):
    """Build the twin-blow-up of PG(2,q) for max degree d (s = d - q - 1 spare slots per vertex)."""
    s = d - q - 1
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl, lp = _incidence_lists(m, edges)
    if s <= 0:
        return n2, list(edges)
    try:
        idx = {p: i for i, p in enumerate(lib.projective_points(q))}
        init = _conic_init(q, idx)
    except Exception:
        init = []
    now = time.monotonic()
    mid = now + (deadline - now) / 2.0
    X = _max_load_set(pl, m, s, rng, mid, init)
    Y = _max_load_set(lp, m, s, rng, deadline, init)
    return _twin_graph(m, edges, pl, lp, X, Y)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = min(0.7 * float(time_limit), 40.0)
    deadline = t0 + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and max degree d.
    best_n, best_E = lib.haar_graph(d, range(d))

    if D >= 3 and d >= 3:
        rng = random.Random(seed * 1000003 + 31 * d + D)
        qs = [q for q in range(2, d) if lib.is_prime_power(q)]  # need q + 1 <= d
        qs.sort(reverse=True)
        for i, q in enumerate(qs):
            now = time.monotonic()
            if now > deadline:
                break
            slice_ = (deadline - now) / (len(qs) - i)
            try:
                n, E = _best_twin_graph(q, d, rng, now + slice_)
            except Exception:
                continue
            if n > best_n and lib.is_valid(n, E, d, D):
                best_n, best_E = n, E

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
