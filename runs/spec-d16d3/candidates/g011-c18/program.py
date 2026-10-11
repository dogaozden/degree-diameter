"""Construction for D = 3 (the target case d = 16).

Base: incidence graph of PG(2, q), with q the largest prime power such that
q + 1 <= d, so it has s = d - q - 1 spare degree on every vertex.

Extension: add an "A" vertex per selected point P (adjacent to the lines through P)
and a "B" vertex per selected line L (adjacent to the points on L). The A-set and
the B-set are chosen independently. A-loads only touch line degrees and B-loads only
touch point degrees, so each side only needs every line (A) or point (B) to carry at
most s selected items. Diameter stays 3 for any such choice, because a copy of P
behaves like a twin of P.

Change from the parent: the two sides are decoupled and searched separately, and
the search runs across all prime powers q, not only the top few. Conics/hyperovals
seed the search. Iterated local search (1-blocker plateau moves, rare 2-blocker
perturbations) refines each side. Every candidate is checked with lib.is_valid
before it is kept, and K_{d,d} is the fallback.

Known limit: for q = 13, s = 2 each side is an arc in PG(2,13) and so has at most
14 points. This family therefore tops out at 2*183 + 2*14 = 394, the record.
Going past it needs a base other than PG(2,q).
"""
import random
import time

import lib


def _incidence(q):
    """Return (m, pts, index, point_lines, line_points) for PG(2, q); points and lines both 0..m-1."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, pts, index, point_lines, line_points


def _conic_set(q, index):
    """Conic plus nucleus (q even): a set meeting every line in at most 2 points."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _loads_ok(S, cons, s, m):
    """True if every constraint id is used by at most s selected items."""
    cnt = [0] * m
    for i in S:
        for c in cons[i]:
            cnt[c] += 1
            if cnt[c] > s:
                return False
    return True


def _greedy(m, s, cons, rng, trials, deadline):
    """Randomised greedy selection with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cnt = [0] * m
        S = []
        for i in order:
            cs = cons[i]
            if all(cnt[c] < s for c in cs):
                S.append(i)
                for c in cs:
                    cnt[c] += 1
        if len(S) > len(best):
            best = S
    return best


def _ils(m, s, cons, rev, S0, rng, deadline):
    """Iterated local search for a larger feasible set, starting from feasible S0.

    rev[c] lists the items that use constraint c. A random outside item i is added
    if feasible. Otherwise the selected items blocking it are removed and i is added,
    but only when there is exactly one blocker (or two, rarely).
    """
    inS = [False] * m
    cnt = [0] * m
    S = []

    def add(i):
        inS[i] = True
        S.append(i)
        for c in cons[i]:
            cnt[c] += 1

    def remove(i):
        inS[i] = False
        S.remove(i)
        for c in cons[i]:
            cnt[c] -= 1

    for i in S0:
        add(i)
    best = list(S)
    it = 0
    while True:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(m)
        if inS[i]:
            continue
        sat = [c for c in cons[i] if cnt[c] >= s]
        if not sat:
            add(i)
        else:
            B = {j for c in sat for j in rev[c] if inS[j]}
            if len(B) == 1 or (len(B) == 2 and rng.random() < 0.05):
                for j in list(B):
                    remove(j)
                add(i)
            else:
                continue
        if len(S) > len(best):
            best = list(S)
    return best


def _best_set(m, s, cons, rev, seeds, rng, t0, t1):
    """Largest feasible set for one side, given seed sets, within the time window [t0, t1]."""
    cands = [S for S in seeds if _loads_ok(S, cons, s, m)]
    S0 = max(cands, key=len, default=[])
    g = _greedy(m, s, cons, rng, 25, t0 + 0.3 * (t1 - t0))
    if len(g) > len(S0) and _loads_ok(g, cons, s, m):
        S0 = g
    S = _ils(m, s, cons, rev, S0, rng, t1)
    if _loads_ok(S, cons, s, m) and len(S) >= len(S0):
        return S
    return S0


def _assemble(m, pg_edges, pl, lp, SA, SB):
    """Incidence graph plus an A-vertex per SA point and a B-vertex per SB line."""
    n = 2 * m + len(SA) + len(SB)
    E = list(pg_edges)
    x = 2 * m
    for P in SA:
        for L in pl[P]:
            E.append((x, m + L))
        x += 1
    for L in SB:
        for Q in lp[L]:
            E.append((Q, x))
        x += 1
    return n, E


def _arc_build(d, rng, deadline):
    """Best (n, edges) over all prime powers q with q + 1 <= d; None if nothing is found."""
    qs = [q for q in range(2, min(d - 1, 25) + 1) if lib.is_prime_power(q) and d - q - 1 >= 0]
    qs.sort(reverse=True)
    best_n, best_e = -1, None
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        s = d - q - 1
        m, pg_n_unused, index, pl, lp = _incidence(q) if False else (None, None, None, None, None)
        m, _, index, pl, lp = _incidence(q)
        pg_edges = lib.projective_plane_incidence(q)[1]
        if s == 0:
            SA, SB = [], []
        else:
            if 2 * m + 2 * (s * m // (q + 1)) <= best_n:
                continue
            seeds = [_conic_set(q, index)] if s >= 2 else []
            SA = _best_set(m, s, pl, lp, seeds, rng, now, now + share / 2)
            SB = _best_set(m, s, lp, pl, seeds, rng, now + share / 2, now + share)
        n, E = _assemble(m, pg_edges, pl, lp, SA, SB)
        if n > best_n:
            best_n, best_e = n, E
    if best_e is None:
        return None
    return best_n, best_e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D <= 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}. Diameter 2, bipartite, degree d.
    best = lib.haar_graph(d, range(d))

    if D == 3:
        res = _arc_build(d, rng, deadline)
        if res is not None:
            n, e = res
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
