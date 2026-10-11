"""Decoupled dual-arc extension of PG(2, q) (diameter 3), with cover growth and saturation.

Idea (new relative to the coupled version): the point-side extension set S1 and the
line-side extension set S2 are chosen independently.

- Each point P in S1 gets a new vertex A_P joined to the q+1 lines through P. Each line
  then gains at most s new neighbours, so S1 must have at most s points on every line.
- Each line L in S2 gets a new vertex B_L joined to the q+1 points on L. Each point then
  gains at most s new neighbours, so S2 must have at most s lines through every point.

Diameter stays 3 for any such choice (A-A and B-B pairs share a line or point; A-B pairs
are within 3 via a line through P meeting L). The coupled version forced S1 = S2 and so
had to satisfy both caps on one set. Decoupling lets each side use its own maximal arc,
here a conic and its dual for odd q, giving 2(q^2+2q+2) vertices when s = 2.

After the extension, cover growth tries to add vertices whose neighbourhoods cover all
vertices within distance D-1, then spare degree is used to saturate opposite-side edges.
Every candidate is checked with lib.is_valid. A K_{d,d} fallback is always valid for D >= 2.

Non-target cases (D >= 4, D <= 2) use the same valid families and fall back to K_{d,d}.
"""
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane data and the decoupled arc sets.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _conic(q, index, F):
    """Conic (plus nucleus for even q) as a vector-index set. Its dual is also an arc of lines."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _loads_ok(S, s, m, cells):
    """True if every cell is loaded by at most s elements of S."""
    load = [0] * m
    for x in S:
        for c in cells[x]:
            load[c] += 1
    return max(load, default=0) <= s


def _greedy_set(m, s, cells, order):
    """Greedy set S in the given order with every cell loaded at most s times."""
    load = [0] * m
    S = []
    for x in order:
        if all(load[c] < s for c in cells[x]):
            S.append(x)
            for c in cells[x]:
                load[c] += 1
    return S


def _seed(m, s, cells, conic, rng, tries=20):
    """Best starting set: the conic if feasible, otherwise the best of several greedy runs."""
    best = list(conic) if _loads_ok(conic, s, m, cells) else []
    order = list(range(m))
    for _ in range(tries):
        rng.shuffle(order)
        S = _greedy_set(m, s, cells, order)
        if len(S) > len(best):
            best = S
    return best


def _local_set(m, s, cells, S0, rng, deadline):
    """Iterated local search for a large S with every cell loaded at most s times.

    Plateau swaps are taken whenever one or two blockers are removed to admit an outside
    element. Returns the largest feasible S seen.
    """
    load = [0] * m
    inS = [False] * m
    S = []

    def add(x):
        inS[x] = True
        S.append(x)
        for c in cells[x]:
            load[c] += 1

    def remove(x):
        inS[x] = False
        S.remove(x)
        for c in cells[x]:
            load[c] -= 1

    for x in S0:
        add(x)
    best = list(S)
    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        sat = {c for c in cells[x] if load[c] >= s}
        if not sat:
            add(x)
        else:
            B = [y for y in S if any(c in sat for c in cells[y])]
            if len(B) == 1 or (len(B) == 2 and rng.random() < 0.1):
                for y in B:
                    remove(y)
                add(x)
            else:
                continue
        if len(S) > len(best):
            best = list(S)
    return best


def _dual_arc_graph(m, edges, point_lines, line_points, S1, S2):
    """PG incidence plus A_P (P in S1, joined to lines through P) and B_L (L in S2, joined to points on L)."""
    n = 2 * m + len(S1) + len(S2)
    E = list(edges)
    for t, P in enumerate(S1):
        a = 2 * m + t
        for L in point_lines[P]:
            E.append((a, m + L))
    base_b = 2 * m + len(S1)
    for t, L in enumerate(S2):
        b = base_b + t
        for Q in line_points[L]:
            E.append((Q, b))
    return n, E


# ----------------------------------------------------------------------------
# Cover-based growth and saturation (diameter-preserving).
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy cover of `full` by at most d candidate vertices; None if it fails."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(60):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Join deficient opposite-side vertices in random order (adding edges never hurts diameter)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    hard = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Baseline: plain PG(2, q) for the largest prime power q with q + 1 <= d.
        qb = next((q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)), None)
        if qb is not None:
            consider(*lib.projective_plane_incidence(qb))

        # Decoupled dual-arc family, for q with spare s = d - q - 1 >= 1.
        qs = [q for q in range(d - 2, 1, -1) if lib.is_prime_power(q)]
        for idx, q in enumerate(qs):
            now = time.monotonic()
            if now >= deadline:
                break
            s = d - q - 1
            m = q * q + q + 1
            kmax = min(m, s * m // (q + 1))
            if 2 * m + 2 * kmax <= best_n:
                continue
            share = (deadline - now) / (len(qs) - idx)
            q_deadline = now + share

            m, edges, pl, lp, index = _pg_data(q)
            F = lib.GF(q)
            conic = _conic(q, index, F)

            while time.monotonic() < q_deadline:
                now = time.monotonic()
                round_end = min(q_deadline, now + max(1.0, 0.5 * share))
                mid = now + (round_end - now) / 2
                S1 = _local_set(m, s, pl, _seed(m, s, pl, conic, rng), rng, mid)
                S2 = _local_set(m, s, lp, _seed(m, s, lp, conic, rng), rng, round_end)
                if not (_loads_ok(S1, s, m, pl) and _loads_ok(S2, s, m, lp)):
                    continue
                n, e = _dual_arc_graph(m, edges, pl, lp, S1, S2)
                consider(n, e)
                n2, e2 = _extend_cover(n, e, d, D, hard, rng)
                e2 = _saturate_edges(n2, e2, d, rng)
                consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
