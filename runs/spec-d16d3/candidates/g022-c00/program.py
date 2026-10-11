"""Family-of-line-sets construction for bipartite diameter-3 graphs.

Start from the incidence graph of PG(2, q), q the largest prime power with q + 1 <= d.
Let s = d - q - 1 be the spare degree of every old vertex. Pick k index sets F_0..F_{k-1}
of projective indices, where each F_i is a set of "lines" (also read as points, since
incidence is the symmetric relation dot(u, v) = 0 on the same vectors) such that:
  * every point lies on a line of F_i (so F_i covers the points),
  * any two sets F_i, F_j share an index (pairwise intersecting),
  * every index lies in at most s sets,
  * |F_i| <= d.
Add A_i (points side) joined to the lines in F_i and B_i (lines side) joined to the points
in F_i. The order is 2(q^2+q+1) + 2k and the diameter stays 3.

Any two sets sharing an index is forced to be a pair structure: one shared index per
pair of sets, plus private "extra" indices. A simulated-annealing search over these slot
assignments grows k one set at a time, starting from the conic arc (k = q+1 = 14 for
d = 16, the known 394 record). Each growth step is verified by lib.is_valid, with a safe
fallback to the PG(2, d-1) incidence graph or K_{d,d}.
"""
import math
import random
import time

import lib


def _pg_data(q):
    """Return (m, point_lines, line_points, index, pts) for PG(2, q); lines and points share indices."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, point_lines, line_points, index, pts


def _conic(q, index):
    """Conic (plus nucleus for even q) as a point-index list."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_init(S, m, line_points):
    """Initial slots from an arc S: pair slots for lines with 2 S-points, extra slots for lines with 1."""
    pos = {P: i for i, P in enumerate(S)}
    on = [[] for _ in range(m)]
    for L in range(m):
        hits = [pos[P] for P in line_points[L] if P in pos]
        if len(hits) > 2:
            return None
        on[L] = hits
    slots = []
    for L in range(m):
        if len(on[L]) == 2:
            a, b = sorted(on[L])
            slots.append(((a, b), L))
        elif len(on[L]) == 1:
            slots.append(((on[L][0],), L))
    return slots


def _grow(k, m, slots, d, rng):
    """Add set k: drop extra slots above the new limit, then add k pair slots and d-k extras."""
    if d - k < 0:
        return None
    limit = d - k
    kept = []
    extras = [0] * k
    for owners, u in slots:
        if len(owners) == 1:
            i = owners[0]
            if extras[i] >= limit:
                continue
            extras[i] += 1
        kept.append((owners, u))
    used = [False] * m
    for _, u in kept:
        used[u] = True
    free = [u for u in range(m) if not used[u]]
    rng.shuffle(free)
    if len(free) <= d:  # need d fresh indices and at least one spare to keep swaps possible
        return None
    p = 0
    for i in range(k):
        kept.append(((i, k), free[p]))
        p += 1
    for _ in range(d - k):
        kept.append(((k,), free[p]))
        p += 1
    return kept


def _apply(cnt, owners, old, new, line_pts):
    """Replace element old by new in the sets listed in owners; return the change in uncovered count."""
    delta = 0
    for i in owners:
        row = cnt[i]
        for t in line_pts[old]:
            row[t] -= 1
            if row[t] == 0:
                delta += 1
        for t in line_pts[new]:
            if row[t] == 0:
                delta -= 1
            row[t] += 1
    return delta


def _anneal(k, m, slots, line_pts, pl, rng, deadline):
    """Simulated annealing over slot elements until every set covers every point. Mutates slots."""
    used = [False] * m
    for _, u in slots:
        used[u] = True
    cnt = [[0] * m for _ in range(k)]
    for owners, u in slots:
        for i in owners:
            row = cnt[i]
            for t in line_pts[u]:
                row[t] += 1
    cost = 0
    for row in cnt:
        cost += sum(1 for c in row if c == 0)
    if cost == 0:
        return True

    slots_of = [[] for _ in range(k)]
    for s, (owners, _) in enumerate(slots):
        for i in owners:
            slots_of[i].append(s)
    nslots = len(slots)

    t_begin = time.monotonic()
    span = max(1e-3, deadline - t_begin)
    T0, T1 = 0.8, 0.08
    T = T0
    it = 0
    while True:
        it += 1
        if (it & 127) == 0:
            now = time.monotonic()
            if now >= deadline:
                return False
            T = T0 * (T1 / T0) ** min(1.0, (now - t_begin) / span)

        if rng.random() < 0.7:
            # Targeted move: fix an uncovered (set, point) pair with a line through that point.
            i = rng.randrange(k)
            row = cnt[i]
            t = -1
            for _ in range(40):
                c = rng.randrange(m)
                if row[c] == 0:
                    t = c
                    break
            if t < 0:
                continue
            s = rng.choice(slots_of[i])
            new = rng.choice(pl[t])
            if used[new]:
                continue
        else:
            s = rng.randrange(nslots)
            new = rng.randrange(m)
            while used[new]:
                new = rng.randrange(m)

        owners, old = slots[s]
        delta = _apply(cnt, owners, old, new, line_pts)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost += delta
            used[old] = False
            used[new] = True
            slots[s] = (owners, new)
            if cost == 0:
                return True
        else:
            _apply(cnt, owners, new, old, line_pts)


def _family(d, q, deadline, rng):
    """Grow a valid family of sets from the conic arc; return (k, slots) for the largest k found."""
    m, point_lines, line_points, index, _pts = _pg_data(q)
    S = _conic(q, index)
    init = _arc_init(S, m, line_points)
    if init is None:
        return None
    k = len(S)
    cur = list(init)
    best = (k, list(cur))
    while time.monotonic() < deadline and k < d:
        ok = False
        while time.monotonic() < deadline:
            nxt = _grow(k, m, cur, d, rng)
            if nxt is None:
                break
            now = time.monotonic()
            stage = max(2.0, 0.5 * (deadline - now))
            if _anneal(k + 1, m, nxt, line_points, point_lines, rng, min(deadline, now + stage)):
                ok = True
                cur = nxt
                break
        if not ok:
            break
        k += 1
        best = (k, list(cur))
    return best


def _graph(m, k, slots):
    """Build the graph: old PG incidence plus A_i (points side) and B_i (lines side) for each set."""
    E = []
    for owners, u in slots:
        for i in owners:
            E.append((2 * m + i, m + u))       # A_i joined to line u
            E.append((u, 2 * m + k + i))       # B_i joined to point u
    return 2 * m + 2 * k, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * time_limit, max(0.5, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3 and d >= 3:
        q = None
        for x in range(d - 1, 1, -1):
            if lib.is_prime_power(x):
                q = x
                break
        if q is not None:
            if q == d - 1:
                consider(*lib.projective_plane_incidence(q))
            s = d - q - 1
            if s >= 2:
                res = _family(d, q, deadline, rng)
                if res is not None:
                    k, slots = res
                    m = q * q + q + 1
                    n, E = _graph(m, k, slots)
                    consider(n, E)

    return best
