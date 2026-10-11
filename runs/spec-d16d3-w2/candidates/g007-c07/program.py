import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graph: projective plane incidence, and the conic arc.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _pg_data(q):
    """Return (m, edges, pts, index, pl, lp) for PG(2, q).

    pl[P] lists the lines through point P; lp[L] lists the points on line L.
    Points and lines share the vector index set 0..m-1.
    """
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pts, index, pl, lp


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _loads_ok(S, s, m, X):
    """True if every index L receives at most s entries from S, where P contributes X[P]."""
    cnt = [0] * m
    for P in S:
        for L in X[P]:
            cnt[L] += 1
    return max(cnt, default=0) <= s


# ----------------------------------------------------------------------------
# NEW: collineation-orbit arc search.
#
# A random matrix M in GL(3, q) permutes the points of PG(2, q) and maps
# incidences to incidences. An arc is then built as a union of whole orbits of
# <M>, so the search space shrinks to orbit choices. Orbit-union greedy gives a
# start point, and an iterated local search (plateau swaps) refines it.
# ----------------------------------------------------------------------------

def _rand_collineation(q, F, rng):
    """Random invertible 3x3 matrix over GF(q)."""
    while True:
        M = [[rng.randrange(q) for _ in range(3)] for _ in range(3)]
        a, b, c = M[0]
        d1, e, f = M[1]
        g, h, i = M[2]
        t1 = F.mul(a, F.sub(F.mul(e, i), F.mul(f, h)))
        t2 = F.mul(b, F.sub(F.mul(d1, i), F.mul(f, g)))
        t3 = F.mul(c, F.sub(F.mul(d1, h), F.mul(e, g)))
        if F.add(F.sub(t1, t2), t3):
            return M


def _collineation_perm(M, pts, index, F):
    """Permutation of point indices induced by the matrix M acting on projective points."""
    out = []
    for v in pts:
        w = []
        for row in M:
            x = 0
            for j in range(3):
                x = F.add(x, F.mul(row[j], v[j]))
            w.append(x)
        c = next(x for x in w if x)
        ic = F.inv(c)
        out.append(index[tuple(F.mul(ic, x) for x in w)])
    return out


def _cycles(perm):
    """Cycles (orbits) of a permutation given as a list."""
    seen = [False] * len(perm)
    out = []
    for i in range(len(perm)):
        if seen[i]:
            continue
        cyc = []
        j = i
        while not seen[j]:
            seen[j] = True
            cyc.append(j)
            j = perm[j]
        out.append(cyc)
    return out


def _orbit_greedy(m, s, X, orbits, rng):
    """Randomized greedy: add whole orbits while every index keeps load <= s."""
    order = sorted(range(len(orbits)), key=lambda i: -len(orbits[i]) * rng.random())
    cnt = [0] * m
    S = []
    for i in order:
        O = orbits[i]
        inc = {}
        for P in O:
            for L in X[P]:
                inc[L] = inc.get(L, 0) + 1
        if all(cnt[L] + c <= s for L, c in inc.items()):
            for L, c in inc.items():
                cnt[L] += c
            S.extend(O)
    return S


def _improve_arc(m, s, X, S0, rng, deadline):
    """Iterated local search: insert a random outside point, evicting its blockers
    when there are at most 1 (or rarely 2). Returns the largest feasible set seen."""
    cnt = [0] * m
    inS = [False] * m
    S = []

    def add(P):
        inS[P] = True
        S.append(P)
        for L in X[P]:
            cnt[L] += 1

    def rem(P):
        inS[P] = False
        S.remove(P)
        for L in X[P]:
            cnt[L] -= 1

    def blockers(P):
        sat = {L for L in X[P] if cnt[L] >= s}
        if not sat:
            return []
        return [R for R in S if any(L in sat for L in X[R])]

    for P in S0:
        add(P)
    best = list(S)
    while time.monotonic() < deadline:
        for _ in range(64):
            P = rng.randrange(m)
            if inS[P]:
                continue
            B = blockers(P)
            if not B:
                add(P)
            elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.05):
                for R in B:
                    rem(R)
                add(P)
            else:
                continue
            if len(S) > len(best):
                best = list(S)
    return best


def _best_side(q, X, m, s, pts, index, F, rng, deadline):
    """Best one-sided arc (every index receives <= s from it) by orbit search, then local search."""
    t0 = time.monotonic()
    orbit_end = t0 + 0.4 * max(0.0, deadline - t0)
    best = []
    while time.monotonic() < orbit_end:
        M = _rand_collineation(q, F, rng)
        orbits = _cycles(_collineation_perm(M, pts, index, F))
        for _ in range(3):
            S = _orbit_greedy(m, s, X, orbits, rng)
            if len(S) > len(best):
                best = S
    if not best:
        best = _orbit_greedy(m, s, X, [[i] for i in range(m)], rng)
    return _improve_arc(m, s, X, best, rng, deadline)


# ----------------------------------------------------------------------------
# Two-sided arc graph (diameter 3).
#
# Points and lines of PG(2, q), plus an A-vertex per element of SA (joined to
# the lines through it) and a B-vertex per element of SB (joined to the points
# on it). SA and SB are chosen independently: SA only needs every line to hold
# <= s points of SA, and SB only needs every point to lie on <= s lines of SB.
# Diameter stays 3 for independent sets, and the bipartition is
# {points, A} vs {lines, B}.
# ----------------------------------------------------------------------------

def _two_arc_graph(m, edges, pl, lp, SA, SB):
    n = 2 * m + len(SA) + len(SB)
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    base = 2 * m + len(SA)
    for t, L in enumerate(SB):
        b = base + t
        for Q in lp[L]:
            E.append((Q, b))
    color = [0] * m + [1] * m + [0] * len(SA) + [1] * len(SB)
    return n, E, color


# ----------------------------------------------------------------------------
# Growth: cover-based vertex addition and saturation of spare degree.
# ----------------------------------------------------------------------------

def _balls(n, adj, r):
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


def _cover(cands, ball, full, d, rng, randomize):
    """Greedy cover of `full` by at most d candidates; None on failure."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        mg = max(gains)
        if mg == 0:
            break
        opts = [i for i, g in enumerate(gains) if g == mg]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, color, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover all vertices within D-1 (keeps diameter <= D)."""
    edges = list(edges)
    color = list(color)
    adj = [[] for _ in range(n)]
    deg = [0] * n
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        deg[u] += 1
        deg[v] += 1
    while time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        chosen = None
        cc = None
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            for attempt in range(30):
                if time.monotonic() >= deadline:
                    break
                chosen = _cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    cc = c
                    break
            if chosen:
                break
        if not chosen:
            break
        v = n
        n += 1
        color.append(1 - cc)
        adj.append([])
        deg.append(0)
        for s in chosen:
            edges.append((s, v))
            adj[s].append(v)
            adj[v].append(s)
            deg[s] += 1
            deg[v] += 1
    return n, edges, color


def _saturate(n, edges, color, d, rng):
    """Randomly join deficient opposite-colour vertices that are not yet adjacent."""
    edges = list(edges)
    deg = [0] * n
    existing = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        existing.add((min(u, v), max(u, v)))
    L = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    R = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in L for b in R if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, color, d, D, deadline, rng):
    """Alternate cover-extension and saturation until neither makes progress."""
    for _ in range(6):
        if time.monotonic() >= deadline:
            break
        n2, e2, c2 = _extend_cover(n, edges, color, d, D, deadline, rng)
        grew = n2 != n
        n, color = n2, c2
        edges = _saturate(n, e2, color, d, rng)
        if not grew:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D < 3:
        return best

    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
        m0 = pg[0] // 2
        n2, e2 = _grow(pg[0], pg[1], [0] * m0 + [1] * m0, d, D,
                       min(deadline, time.monotonic() + 0.05 * time_limit), rng)
        consider(n2, e2)

    if D == 3:
        # Keep only q whose counting bound 2m + 2*floor(s*m/(q+1)) can beat the current best.
        qs = []
        for q in range(min(d - 1, 23), 1, -1):
            if not lib.is_prime_power(q):
                continue
            s = d - q - 1
            if s < 1:
                continue
            m = q * q + q + 1
            if 2 * m + 2 * (s * m // (q + 1)) > best_n:
                qs.append(q)

        for idx, q in enumerate(qs):
            now = time.monotonic()
            if now >= deadline:
                break
            share = (deadline - now) / (len(qs) - idx)
            s = d - q - 1
            m, edges, pts, index, pl, lp = _pg_data(q)
            F = lib.GF(q)
            SA = _best_side(q, pl, m, s, pts, index, F, rng, now + 0.4 * share)
            SB = _best_side(q, lp, m, s, pts, index, F, rng, now + 0.8 * share)

            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, pl) and len(cs) > len(SA):
                SA = cs
            if _loads_ok(cs, s, m, lp) and len(cs) > len(SB):
                SB = cs
            if not SA or not SB:
                continue

            n, e, color = _two_arc_graph(m, edges, pl, lp, SA, SB)
            consider(n, e)
            n2, e2 = _grow(n, _saturate(n, e, color, d, rng), color, d, D,
                           now + share, rng)
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
