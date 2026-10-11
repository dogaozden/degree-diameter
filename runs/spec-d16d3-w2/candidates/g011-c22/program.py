import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Main D = 3 route: Haar graphs from difference covers, found by tabu search.
#
# H(m, S) has parts A = Z_m and B = Z_m with a_i ~ b_{i+s} for s in S. It is
# d-regular, bipartite, and has diameter <= 3 iff S - S = Z_m. The search keeps
# the cover count of S - S and swaps elements under a short tabu list.
# ----------------------------------------------------------------------------

def _diff_counts(S, m):
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    return cnt


def _swap(cnt, S, i, y, m):
    """Replace S[i] by y (updating cnt). Returns the change in the number of uncovered differences."""
    x = S[i]
    others = S[:i] + S[i + 1:]
    delta = 0
    for s in others:
        for g in ((x - s) % m, (s - x) % m):
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
    for s in others:
        for g in ((y - s) % m, (s - y) % m):
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
    S[i] = y
    return delta


def _tabu_cover(k, m, rng, deadline):
    """Find S subset of Z_m with |S| = k and S - S = Z_m, or None on timeout."""
    if m < k:
        return None
    if m == k:
        return list(range(m))
    S = rng.sample(range(m), k)
    cnt = _diff_counts(S, m)
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    tabu = {}
    it = 0
    best_unc = unc
    while unc > 0:
        it += 1
        if (it & 63) == 0 and time.monotonic() > deadline:
            return None
        inS = set(S)
        cand = None
        for _ in range(40):
            i = rng.randrange(k)
            y = rng.randrange(m)
            if y in inS:
                continue
            x = S[i]
            d1 = _swap(cnt, S, i, y, m)
            _swap(cnt, S, i, x, m)  # revert
            if tabu.get(y, 0) > it and unc + d1 >= best_unc:
                continue  # tabu and not an aspiration improvement
            if cand is None or d1 < cand[0]:
                cand = (d1, i, y)
        if cand is None:
            continue
        d1, i, y = cand
        x = S[i]
        unc += _swap(cnt, S, i, y, m)
        tabu[x] = it + rng.randint(3, 8)
        if unc < best_unc:
            best_unc = unc
    return sorted(S)


def _haar_search(k, rng, deadline):
    """Find the largest m with a difference cover of size k in Z_m; returns (m, S) or None."""
    if k < 2:
        return None
    mmax = k * (k - 1) + 1
    start = max(k, int(0.8 * mmax))

    def attempt(m):
        rem = deadline - time.monotonic()
        if rem <= 0:
            return None
        return _tabu_cover(k, m, rng, time.monotonic() + max(1.0, rem / 4.0))

    best = None
    S = attempt(start)
    if S is not None:
        best = (start, S)
        m = start + 1
        while m <= mmax and time.monotonic() < deadline:
            S = attempt(m)
            if S is None:
                break
            best = (m, S)
            m += 1
    else:
        m = start - 1
        while m >= k and time.monotonic() < deadline:
            S = attempt(m)
            if S is not None:
                best = (m, S)
                break
            m -= 1
    return best


# ----------------------------------------------------------------------------
# Secondary D = 3 route: PG(2,q) incidence graph extended by an arc (parent idea).
# ----------------------------------------------------------------------------

def _pg(q):
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _loads_ok(S, s, m, pl, lp):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, pl, lp, rng, trials):
    best = []
    order = list(range(m))
    for _ in range(trials):
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index):
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_candidates(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q) or time.monotonic() > deadline:
            continue
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp = _pg(q)
        cands = [[], _greedy_arc(m, s, pl, lp, rng, 30)]
        if s >= 2:
            pts = lib.projective_points(q)
            index = {p: i for i, p in enumerate(pts)}
            cands.append(_conic_set(q, index))
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        k = len(S)
        n = 2 * m + 2 * k
        E = list(edges)
        for t, P in enumerate(S):
            a = 2 * m + t
            for L in pl[P]:
                E.append((a, m + L))
        for t, j in enumerate(S):
            b = 2 * m + k + t
            for Q in lp[j]:
                E.append((Q, b))
        out.append((n, E))
    return out


# ----------------------------------------------------------------------------
# D >= 4 baseline: generalized quadrangle W(q) incidence graph (diameter 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.75 * float(time_limit), 45.0)
    deadline = start + budget
    rng = random.Random(seed * 1000003 + 17 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D == 3 and d >= 2:
        res = _haar_search(d, rng, start + 0.6 * budget)
        if res is not None:
            m, S = res
            consider(*lib.haar_graph(m, S))
        for n_c, E_c in _arc_candidates(d, start + 0.85 * budget, random.Random(seed * 7919 + d)):
            consider(n_c, E_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
