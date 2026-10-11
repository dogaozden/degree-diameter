import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# NEW: weighted star extension of PG(2,q)
#
# PG(2,q) incidence graph: (q+1)-regular, diameter 3, points 0..m-1, lines 0..m-1.
# Spare degree per vertex is s = d - (q+1).
#   * A "star" x_P (side 0) is joined to all q+1 lines through point P.
#   * An "axis" y_L (side 1) is joined to all q+1 points on line L.
# Degree: line M gains sum_{P on M} wX[P]; point P gains sum_{L through P} wY[L].
# Both must be <= s, so wX and wY are integer packings: every line (resp. point)
# carries total weight <= s. Each packing is searched by simulated annealing.
# Distances: same-side pairs share a neighbour (line PQ, point L∩K, ...), and
# opposite-side pairs are at distance 1 or 3, so the diameter stays 3.
# ----------------------------------------------------------------------------

def _pg(q):
    """Return (m, edges, lines_of, pts_of) for PG(2,q); points and lines are both indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    lines_of = [[] for _ in range(m)]
    pts_of = [[] for _ in range(m)]
    for u, v in edges:
        lines_of[u].append(v - m)
        pts_of[v - m].append(u)
    return m, edges, lines_of, pts_of


def _index_and_field(q):
    pts = lib.projective_points(q)
    return {p: i for i, p in enumerate(pts)}, lib.GF(q)


def _conic_set(q, index, F):
    """Conic plus nucleus (q even): an arc, so every line holds at most 2 of them."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _dual_conic_set(q, index, F):
    """Dual conic: lines (1, 2t, t^2) and (0,0,1); a dual arc for odd q."""
    two = F.add(1, 1)
    S = [index[(1, F.mul(two, t), F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    return S


def _valid_init(w, s, item_cons, nc):
    load = [0] * nc
    for i, x in enumerate(w):
        if x:
            for c in item_cons[i]:
                load[c] += x
    return max(load, default=0) <= s


def _pack(item_cons, cons_items, s, w0, rng, deadline):
    """Simulated annealing for a max-weight packing: weights in 0..s with each constraint's total <= s.

    An add move on item i removes random units from overloaded constraints when needed.
    Returns the best weight vector found.
    """
    ni = len(item_cons)
    w = list(w0)
    load = [0] * len(cons_items)
    for i in range(ni):
        if w[i]:
            for c in item_cons[i]:
                load[c] += w[i]
    cur = sum(w)
    best, best_w = cur, list(w)
    if s <= 0 or ni == 0:
        return best_w
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = 0.6
    it = 0
    while True:
        it += 1
        if not (it & 255):
            now = time.monotonic()
            if now >= deadline:
                break
            frac = min(1.0, (now - t0) / span)
            T = 0.6 * (1.0 - frac) + 0.05 * frac
        i = rng.randrange(ni)
        if w[i] >= s:
            continue
        changed = []
        ok = True
        for c in item_cons[i]:
            while load[c] >= s:
                cand = [j for j in cons_items[c] if j != i and w[j] > 0]
                if not cand:
                    ok = False
                    break
                j = rng.choice(cand)
                w[j] -= 1
                for c2 in item_cons[j]:
                    load[c2] -= 1
                changed.append(j)
            if not ok:
                break
        if ok:
            delta = 1 - len(changed)
            if delta >= 0 or rng.random() < math.exp(delta / T):
                w[i] += 1
                for c in item_cons[i]:
                    load[c] += 1
                cur += delta
                if cur > best:
                    best = cur
                    best_w = list(w)
                continue
        for j in reversed(changed):
            w[j] += 1
            for c2 in item_cons[j]:
                load[c2] += 1
    return best_w


def _star_graph(q, d, rng, deadline):
    """Build PG(2,q) plus weighted stars (side 0) and axes (side 1) for degree d."""
    s = d - (q + 1)
    if s < 0:
        return 0, []
    m, edges, lines_of, pts_of = _pg(q)
    index, F = _index_and_field(q)
    w_pts = [0] * m
    for P in _conic_set(q, index, F):
        w_pts[P] = 1
    w_lines = [0] * m
    for L in _dual_conic_set(q, index, F):
        w_lines[L] = 1
    if not _valid_init(w_pts, s, lines_of, m):
        w_pts = [0] * m
    if not _valid_init(w_lines, s, pts_of, m):
        w_lines = [0] * m
    now = time.monotonic()
    mid = now + max(0.0, deadline - now) / 2
    wX = _pack(lines_of, pts_of, s, w_pts, rng, mid)
    wY = _pack(pts_of, lines_of, s, w_lines, rng, deadline)
    n = 2 * m
    E = list(edges)
    for P in range(m):
        for _ in range(wX[P]):
            x = n
            n += 1
            E.extend((x, m + L) for L in lines_of[P])
    for L in range(m):
        for _ in range(wY[L]):
            y = n
            n += 1
            E.extend((P, y) for P in pts_of[L])
    return n, E


# ----------------------------------------------------------------------------
# Haar graphs from difference covers (D = 3)
# ----------------------------------------------------------------------------

def _cover_search(k, m, rng, deadline):
    """Find S subset of Z_m with |S| = k and S - S = Z_m. Returns sorted S, or None."""
    if m < k:
        return None
    if m == k:
        return list(range(m))
    S = rng.sample(range(m), k)
    in_s = set(S)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    T = 1.0
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        if it % 150000 == 0:
            T = 0.5
        T = max(0.05, T * 0.9999)
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(m)
        if y in in_s:
            continue
        others = S[:i] + S[i + 1:]
        delta = 0
        for s in others:
            g = (x - s) % m
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
            g = (s - x) % m
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
        for s in others:
            g = (y - s) % m
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
            g = (s - y) % m
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            in_s.discard(x)
            in_s.add(y)
            unc += delta
        else:
            for s in others:
                cnt[(y - s) % m] -= 1
                cnt[(s - y) % m] -= 1
            for s in others:
                cnt[(x - s) % m] += 1
                cnt[(s - x) % m] += 1
    return sorted(S)


def _haar_search(k, rng, deadline):
    """Climb m upward from a high start, keeping the largest m with a difference cover. Returns (m, S) or None."""
    if k < 2:
        return None
    mmax = k * (k - 1) + 1
    m = max(k, int(0.8 * mmax))
    best = None
    fails = 0
    while m <= mmax and time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        slice_ = max(0.5, remaining / 3.0)
        S = _cover_search(k, m, rng, min(deadline, time.monotonic() + slice_))
        if S is not None:
            best = (m, S)
            fails = 0
        else:
            fails += 1
            if fails >= 2:
                break
        m += 1
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4)
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * float(time_limit), 40.0)
    deadline = start + budget
    rng = random.Random(seed * 1000003 + 17 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D == 3:
        # Primary: weighted star extensions of PG(2,q) for every prime power q with q+1 <= d.
        qs = [q for q in range(2, min(d - 1, 25) + 1) if lib.is_prime_power(q)]
        qs.sort(reverse=True)
        star_end = start + 0.55 * budget
        for idx, q in enumerate(qs):
            now = time.monotonic()
            if now >= star_end:
                break
            slot_end = now + (star_end - now) / (len(qs) - idx)
            n_c, E_c = _star_graph(q, d, rng, slot_end)
            consider(n_c, E_c)
        # Secondary: Haar graph from a difference cover of size d.
        if d >= 2:
            res = _haar_search(d, rng, start + 0.85 * budget)
            if res is not None:
                m_h, S = res
                consider(*lib.haar_graph(m_h, S))

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
