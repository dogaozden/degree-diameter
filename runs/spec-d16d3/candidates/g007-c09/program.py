import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane data.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); points and lines are both indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _conic_init(q):
    """Conic (plus nucleus for even q) as an index set: an arc with no three collinear."""
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


# ----------------------------------------------------------------------------
# Decoupled extension of PG(2, q).
#
# Add an A-vertex per point P in SA (joined to the q+1 lines through P) and a
# B-vertex per line L in SB (joined to the q+1 points on L). A-vertices and
# B-vertices never touch each other, so SA and SB are chosen independently:
#   - SA: every line may carry at most s points of SA (line degree q+1+load <= d)
#   - SB: every point may lie on at most s lines of SB
# Diameter stays 3 for any such choice (checked by lib.is_valid anyway).
# ----------------------------------------------------------------------------

def _ls_loads(m, s, elem_cover, cover_elem, rng, deadline, init, iters):
    """Large set X of indices with every cover index hit at most s times.

    elem_cover[x] lists the cover indices touched by x; cover_elem[c] lists the x touching c.
    Plateau local search: add a random x; if it overloads, evict one common member
    (a 1-swap). Returns the largest feasible set seen.
    """
    inX = [False] * m
    load = [0] * m
    X = []

    def add(x):
        inX[x] = True
        X.append(x)
        for c in elem_cover[x]:
            load[c] += 1

    def drop(x):
        inX[x] = False
        X.remove(x)
        for c in elem_cover[x]:
            load[c] -= 1

    for x in init:
        if not inX[x] and all(load[c] < s for c in elem_cover[x]):
            add(x)
    best = list(X)

    for _ in range(iters):
        if len(X) == m or time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inX[x]:
            continue
        conf = [c for c in elem_cover[x] if load[c] >= s]
        if conf:
            common = None
            for c in conf:
                mem = {y for y in cover_elem[c] if inX[y]}
                common = mem if common is None else (common & mem)
                if not common:
                    break
            if not common:
                continue
            drop(rng.choice(sorted(common)))
        add(x)
        if len(X) > len(best):
            best = list(X)
    return best


def _build_decoupled(m, edges, point_lines, line_points, SA, SB):
    """Projective plane plus A-vertices (over SA) and B-vertices (over SB)."""
    n = 2 * m + len(SA) + len(SB)
    E = list(edges)
    base = 2 * m + len(SA)
    for t, P in enumerate(SA):
        x = 2 * m + t
        E.extend((x, m + L) for L in point_lines[P])
    for t, L in enumerate(SB):
        b = base + t
        E.extend((Q, b) for Q in line_points[L])
    return n, E


# ----------------------------------------------------------------------------
# Cover-based vertex growth (diameter-preserving).
# A new vertex joined to a set covering every vertex within distance D-1 keeps
# diameter D. Only opposite-side vertices with spare degree are used.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


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


def _cover(cands, ball, full, d, rng, tries):
    """Randomized greedy cover of `full` by at most d candidates; None if all tries fail."""
    if not cands:
        return None
    for t in range(tries):
        pool = list(cands)
        if t:
            rng.shuffle(pool)
        covered = 0
        chosen = []
        while covered != full and len(chosen) < d and pool:
            gains = [(ball[s] & ~covered).bit_count() for s in pool]
            i = max(range(len(pool)), key=gains.__getitem__)
            if gains[i] == 0:
                break
            s = pool.pop(i)
            chosen.append(s)
            covered |= ball[s]
        if covered == full:
            return chosen
    return None


def _grow(n, edges, d, D, deadline, rng):
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        deg = [len(a) for a in adj]
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        grown = False
        for c in (0, 1):
            cands = [x for x in range(n) if color[x] == c and deg[x] < d]
            chosen = _cover(cands, ball, full, d, rng, 20)
            if chosen:
                v = n
                n += 1
                adj.append([])
                color.append(1 - c)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                grown = True
                break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 6.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg_cache = {}

        def pg(q):
            if q not in pg_cache:
                pg_cache[q] = _pg_data(q)
            return pg_cache[q]

        qs_all = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]
        if qs_all:
            # Plain incidence graph of PG(2, q) for the largest usable q.
            m, e, _, _ = pg(qs_all[-1])
            consider(2 * m, e)

        # Decoupled arc extensions for every q leaving spare degree s >= 1.
        cands = [q for q in qs_all if d - q - 1 >= 1]
        total = max(1.0, deadline - time.monotonic())
        slice_len = max(1.0, total / (3.0 * max(1, len(cands))))
        rounds = 0
        seen_init = set()
        while cands and time.monotonic() < deadline - 0.5:
            q = cands[rounds % len(cands)]
            rounds += 1
            s = d - q - 1
            m, edges, pl, lp = pg(q)

            now = time.monotonic()
            slice_end = min(deadline, now + slice_len)
            half = now + (slice_end - now) / 2.0
            init = _conic_init(q) if (s >= 2 and q not in seen_init) else []
            seen_init.add(q)

            SA = _ls_loads(m, s, pl, lp, rng, half, init, 5_000_000)
            SB = _ls_loads(m, s, lp, pl, rng, slice_end, init, 5_000_000)

            n, E = _build_decoupled(m, edges, pl, lp, SA, SB)
            consider(n, E)
            n2, E2 = _grow(n, E, d, D, deadline, rng)
            consider(n2, E2)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
