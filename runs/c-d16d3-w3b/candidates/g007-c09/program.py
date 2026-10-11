import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy A (new, bold): bi-Cayley Haar graphs over Z_m.
#
# H(Z_m, S) has vertices A_i and B_i (i in Z_m), with A_i ~ B_{i+s} for s in S.
# It is bipartite and |S| = d regular. A_x and A_y are at distance 2 exactly when
# y - x is a difference s - t, and A_x to B_h is at distance <= 3 whenever
# h - s' is a difference for some s' in S. So if S - S covers all of Z_m,
# the diameter is 3. This needs m <= d(d-1)+1, which gives order up to 2(d^2-d+1).
# For d = 16 that is 482, the Moore bound. We search for difference covers
# S with simulated annealing and climb m upward.
#
# Strategy B (parent, kept as safe fallback): PG(2,q) incidence graphs extended
# by arc vertices on both sides, with optional matching deletions.
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
    """Best capacitated set found by greedy, supplied seeds, then local search."""
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
    """Yield (n, edges) candidates from arc-extended projective planes."""
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
# Difference-cover search for Haar graphs.
# ----------------------------------------------------------------------------

def _apply(cnt, others, x, m, sign):
    """Add (sign=+1) or remove (sign=-1) the differences between x and each element of others.

    Returns the change in the number of uncovered nonzero residues.
    """
    delta = 0
    for t in others:
        for y in ((x - t) % m, (t - x) % m):
            if sign < 0:
                cnt[y] -= 1
                if cnt[y] == 0:
                    delta += 1
            else:
                if cnt[y] == 0:
                    delta -= 1
                cnt[y] += 1
    return delta


def _sa_cover(d, m, rng, deadline):
    """Find S subset of Z_m, |S| = d, 0 in S, with S - S = Z_m, by simulated annealing. None on failure."""
    if m < d:
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)
    if unc == 0:
        return S
    t0 = time.monotonic()
    span = max(1e-9, deadline - t0)
    T = 0.5
    it = 0
    while True:
        it += 1
        if (it & 255) == 0:
            now = time.monotonic()
            if now > deadline:
                return None
            frac = (now - t0) / span
            T = 0.5 * (1.0 - frac) + 0.05
        i = rng.randrange(1, d)
        old = S[i]
        v = rng.randrange(1, m)
        if v in S:
            continue
        others = S[:i] + S[i + 1:]
        delta = _apply(cnt, others, old, m, -1)
        delta += _apply(cnt, others, v, m, +1)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = v
            unc += delta
            if unc == 0:
                return S
        else:
            _apply(cnt, others, v, m, -1)
            _apply(cnt, others, old, m, +1)


def _climb(d, deadline, rng):
    """Increase m while a difference cover of Z_m with d elements is found. Returns (m, S) or None."""
    cap = d * (d - 1) + 1
    m = max(d, int(0.7 * cap))
    best = None
    while m <= cap:
        now = time.monotonic()
        if now >= deadline:
            break
        budget = max(0.5, 0.4 * (deadline - now))
        S = _sa_cover(d, m, rng, min(deadline, now + budget))
        if S is None:
            break
        best = (m, sorted(S))
        m += 1
    return best


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
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    if D >= 3:
        # Strategy B: arc-extended projective planes (parent construction), small share of time.
        try:
            arc_deadline = start + 0.3 * time_limit
            for n_c, e_c in _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d)):
                if n_c > best_n:
                    consider(n_c, e_c)
        except Exception:
            pass

        # Strategy A: Haar graphs from difference covers, the main attack.
        try:
            res = _climb(d, start + 0.8 * time_limit, rng)
            if res is not None:
                m, S = res
                n_c, e_c = lib.haar_graph(m, S)
                consider(n_c, e_c)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
