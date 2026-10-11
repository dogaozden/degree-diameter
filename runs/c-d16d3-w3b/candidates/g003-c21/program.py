"""Diameter-3 bipartite search: cyclic / abelian Haar (Cayley) graphs with difference covers.

New construction for D = 3 (the d = 16 target). For an abelian group G of order m and a
set S of size d containing 0, the Haar graph H(G, S) has a-vertices x and b-vertices y, with
x adjacent to y iff y - x is in S. It is d-regular and bipartite on 2m vertices. Its
diameter is at most 3 exactly when
    S - S = G   (a-a and b-b pairs at distance <= 2)
    S - S + S = G   (a-b pairs at distance <= 3).
So we search for a difference cover of G of size d, for the largest m possible. The
Moore bound gives m <= d(d-1)+1, so for d = 16 the ceiling is m = 241 (order 482).

Pipeline for D >= 3:
  1. Arc-extended projective-plane graphs (previous construction, kept as a safe baseline).
  2. Descending search over m for an abelian difference cover; the first success that
     beats the current best is kept. Every candidate is checked with lib.is_valid.
For D = 4 the generalized quadrangle W(q) is also tried. The K_{d,d} fallback is always
valid for D >= 2. Every returned graph is validated.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), with deletions.
# (Carried over from the parent program.)
# ----------------------------------------------------------------------------

_LS_ITERS = 12000


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


def _loads_ok(S, caps, nbr):
    """True if every target t is hit by <= caps[t] elements of S."""
    m = len(caps)
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return all(load[t] <= caps[t] for t in range(m))


def _greedy_side(m, caps, nbr, rng, trials, deadline):
    """Randomized greedy capacitated set."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < caps[t] for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_search(m, caps, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the capacitated set problem."""
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= caps[t]:
                if not cur:
                    ok = False
                    break
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _best_side(m, caps, nbr, rng, deadline, seeds):
    """Best capacitated set from greedy, supplied seeds, then local search."""
    cands = [_greedy_side(m, caps, nbr, rng, 12, deadline)]
    for S in seeds:
        if _loads_ok(S, caps, nbr):
            cands.append(list(S))
    start = max(cands, key=len)
    return _local_search(m, caps, nbr, start, rng, deadline, _LS_ITERS)


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _pick_deletions(edges, m, r, rng):
    """Random matching of up to r PG incidences, as (point, line) pairs."""
    inc = [(u, v - m) for u, v in edges]
    rng.shuffle(inc)
    usedP, usedL, R = set(), set(), []
    for P, L in inc:
        if len(R) >= r:
            break
        if P in usedP or L in usedL:
            continue
        usedP.add(P)
        usedL.add(L)
        R.append((P, L))
    return R


def _arc_graph(m, edges, R, point_lines, line_points, SA, SB):
    """PG incidence minus deleted matching R, plus A-vertices and B-vertices."""
    Rset = set(R)
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = [(u, v) for u, v in edges if (u, v - m) not in Rset]
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Candidates (n, edges) from arc-extended PG(2, q) for prime powers q with q + 1 <= d."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * (s + 1) * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        q_deadline = now + (deadline - now) / (len(qs) - idx)
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        conic = _conic_set(q, index, lib.GF(q)) if s >= 0 else []
        rs = [0, max(1, m // 12), max(1, m // 6), max(1, m // 4)]
        trial = 0
        while time.monotonic() < q_deadline:
            r = rs[trial] if trial < len(rs) else rng.choice(rs)
            trial += 1
            R = _pick_deletions(edges, m, r, rng) if r > 0 else []
            delP = [0] * m
            delL = [0] * m
            for P, L in R:
                delP[P] += 1
                delL[L] += 1
            capL = [s + delL[L] for L in range(m)]
            capP = [s + delP[P] for P in range(m)]
            seeds = [conic] if not R else []
            SA = _best_side(m, capL, point_lines, rng, q_deadline, seeds)
            SB = _best_side(m, capP, line_points, rng, q_deadline, seeds)
            if not (_loads_ok(SA, capL, point_lines) and _loads_ok(SB, capP, line_points)):
                continue
            out.append(_arc_graph(m, edges, R, point_lines, line_points, SA, SB))
            if trial > 40:
                break
    out.sort(key=lambda t: -t[0])
    return out[:30]


# ----------------------------------------------------------------------------
# NEW: abelian difference-cover Haar graphs for diameter 3.
# ----------------------------------------------------------------------------

def _group_tables(a, b):
    """Addition and negation tables for Z_a x Z_b, element i*b + j."""
    m = a * b

    def add(x, y):
        return ((x // b + y // b) % a) * b + (x % b + y % b) % b

    A = [[add(x, y) for y in range(m)] for x in range(m)]
    N = [0] * m
    for x in range(m):
        i, j = divmod(x, b)
        N[x] = ((-i) % a) * b + (-j) % b
    return A, N


def _apply(cnt, others, y, A, N, step):
    """Add (step > 0) or remove (step < 0) the differences between y and every element of others.

    Returns the change in the number of uncovered nonzero differences.
    """
    z = 0
    for t in others:
        for g in (A[t][N[y]], A[y][N[t]]):
            if step > 0:
                if cnt[g] == 0:
                    z -= 1
                cnt[g] += 1
            else:
                cnt[g] -= 1
                if cnt[g] == 0:
                    z += 1
    return z


def _search(m, d, A, N, rng, deadline, max_moves):
    """Annealing-style search for S (size d, containing 0) with S - S = G."""
    S = [0] + rng.sample(range(1, m), d - 1)
    cnt = [0] * m
    unc = m - 1
    added = []
    for s in S:
        unc += _apply(cnt, added, s, A, N, 1)
        added.append(s)
    T = 0.35
    for it in range(max_moves):
        if unc == 0:
            return S
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        old = S[i]
        others = S[:i] + S[i + 1:]
        d1 = _apply(cnt, others, old, A, N, -1)
        d2 = _apply(cnt, others, x, A, N, 1)
        delta = d1 + d2
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = x
            unc += delta
        else:
            _apply(cnt, others, x, A, N, -1)
            _apply(cnt, others, old, A, N, 1)
    return S if unc == 0 else None


def _covers3(S, m, A, N):
    """True if S - S + S covers the whole group."""
    D2 = {A[s][N[t]] for s in S for t in S}
    return len({A[u][v] for u in D2 for v in S}) == m


def _cover_search(d, min_m, deadline, rng):
    """Descend from the Moore-type bound m = d(d-1)+1; return (a, b, S) for the first success above min_m."""
    ub = d * (d - 1) + 1
    cache = {}
    for m in range(ub, max(min_m, d - 1), -1):
        if time.monotonic() > deadline:
            return None
        divs = [a for a in range(1, m + 1) if m % a == 0]
        for _ in range(4):
            if time.monotonic() > deadline:
                return None
            a = rng.choice(divs)
            b = m // a
            if (a, b) not in cache:
                cache[(a, b)] = _group_tables(a, b)
            A, N = cache[(a, b)]
            S = _search(m, d, A, N, rng, deadline, 4000)
            if S is not None and _covers3(S, m, A, N):
                return a, b, S
    return None


def _cayley_graph(a, b, S):
    """Haar graph of Z_a x Z_b with connection set S: a-vertex x adjacent to b-vertex x + s."""
    m = a * b
    A, _ = _group_tables(a, b)
    E = []
    for x in range(m):
        for s in S:
            E.append((x, m + A[x][s]))
    return 2 * m, E


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4). (Carried over from the parent program.)
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # 1. Arc-extended projective plane graphs (baseline construction).
        arc_deadline = start + 0.35 * time_limit
        for n_c, e_c in _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d)):
            if n_c > best_n:
                consider(n_c, e_c)

        # 2. New construction: abelian difference-cover Haar graphs, searching m downward.
        #    Only m with 2m > current best can improve the result.
        haar_deadline = start + 0.8 * time_limit
        res = _cover_search(d, best_n // 2, haar_deadline, rng)
        if res is not None:
            a, b, S = res
            n_h, e_h = _cayley_graph(a, b, S)
            consider(n_h, e_h)

    if D >= 4 and time.monotonic() < start + 0.85 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
