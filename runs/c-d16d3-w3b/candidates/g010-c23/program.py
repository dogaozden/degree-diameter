import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Cyclic Haar graphs via difference covers (diameter 3).
#
# Haar graph H(Z_m, S): a_i ~ b_{i+s} for s in S, |S| = d, so it is d-regular
# and bipartite. Same-side distances need every nonzero x in Z_m to be a
# difference s - t (s != t in S). If S - S covers Z_m, then every a-a and b-b
# pair is at distance <= 2, and every a-b pair is at distance <= 3 (because
# S - S + S covers Z_m). So a difference cover of size d in Z_m gives a valid
# graph of order 2m. The search bisects on m and runs simulated annealing on S.
# ----------------------------------------------------------------------------

def _upd(cnt, m, e, others, sign):
    """Add (sign=+1) or remove (sign=-1) the ordered differences between e and each element of others.

    cnt[x] counts ordered pairs (s, t), s != t, with s - t = x mod m. Returns the change in
    the number of uncovered nonzero residues.
    """
    du = 0
    for t in others:
        for z in ((e - t) % m, (t - e) % m):
            if sign > 0:
                if cnt[z] == 0:
                    du -= 1
                cnt[z] += 1
            else:
                cnt[z] -= 1
                if cnt[z] == 0:
                    du += 1
    return du


def _cover_try(m, k, rng, deadline):
    """Simulated annealing for a k-subset S of Z_m with S - S = Z_m. Returns sorted S or None."""
    if k < 2 or k > m:
        return None
    S = [0] + rng.sample(range(1, m), k - 1)
    inS = [False] * m
    for s in S:
        inS[s] = True
    cnt = [0] * m
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)
    T = 0.35
    it = 0
    while unc > 0:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            return None
        idx = rng.randrange(1, k)          # element 0 stays fixed (translation invariance)
        old = S[idx]
        new = rng.randrange(1, m)
        if inS[new]:
            continue
        others = [S[i] for i in range(k) if i != idx]
        du = _upd(cnt, m, old, others, -1) + _upd(cnt, m, new, others, 1)
        if du <= 0 or rng.random() < math.exp(-du / T):
            S[idx] = new
            inS[old] = False
            inS[new] = True
            unc += du
        else:
            _upd(cnt, m, new, others, -1)
            _upd(cnt, m, old, others, 1)
    return sorted(S)


def _haar_search(d, deadline, rng):
    """Bisect on m in [d, d(d-1)+1] for the largest m with a size-d difference cover. Returns (m, S)."""
    k = d
    lo = k
    best = (k, list(range(k)))  # S = all of Z_k: valid, gives K_{d,d}
    hi = k * (k - 1) + 1
    while lo < hi and time.monotonic() < deadline:
        mid = (lo + hi + 1) // 2
        remaining = deadline - time.monotonic()
        budget = min(4.0, remaining / 2)
        S = _cover_try(mid, k, rng, time.monotonic() + budget)
        if S is not None:
            lo = mid
            best = (mid, S)
        else:
            hi = mid - 1
    return best


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), with deletions.
# (Parent construction, kept as a fallback candidate generator.)
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
    """True if every target t is hit by <= caps[t] elements of S, where element x hits nbr[x]."""
    m = len(caps)
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return all(load[t] <= caps[t] for t in range(m))


def _greedy_side(m, caps, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target t is hit by <= caps[t] chosen elements."""
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
    """Plateau/improvement local search for the capacitated set problem. Returns the best valid set seen."""
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
    """Random matching of up to r PG incidences, as (point, line) pairs with line index 0..m-1."""
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
    """PG incidence minus deleted matching R, plus one new A-vertex per SA point and one B-vertex per SB line."""
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
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
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


def _largest_prime_power_at_most(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    haar_deadline = start + 0.50 * time_limit
    arc_deadline = start + 0.72 * time_limit
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
        # 1. Cyclic Haar graphs from difference covers (new main search).
        m, S = _haar_search(d, haar_deadline, rng)
        if m > best_n // 2:
            n_h, e_h = lib.haar_graph(m, S)
            consider(n_h, e_h)

        # 2. Projective plane incidence graph of PG(2, q), q + 1 <= d.
        q = _largest_prime_power_at_most(d - 1)
        if q is not None and 2 * (q * q + q + 1) > best_n:
            n_p, e_p = lib.projective_plane_incidence(q)
            consider(n_p, e_p)

        # 3. Arc-extended projective plane graphs (parent construction).
        if time.monotonic() < arc_deadline:
            cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
            for n_c, e_c in cands:
                if n_c > best_n:
                    consider(n_c, e_c)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
