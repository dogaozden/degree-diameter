import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane data and the arc-extension construction (diameter 3).
#
# Points and lines of PG(2, q) are both indexed 0..m-1 by the same vectors.
# Point P lies on line j iff the dot product is zero. For a set S of point
# indices, let load(j) = |S ∩ line j|. If every load is <= s = d - q - 1, then
# for each P in S add an A-vertex joined to the q+1 lines through P, and for
# each j in S add a B-vertex joined to the q+1 points on line j. Every old
# vertex then has degree <= d. The result is bipartite with diameter 3, and
# the order is 2m + 2|S|.
#
# Searching for S is a maximum (k, s)-arc problem. A simulated-annealing
# local search adds a random point and evicts one member from each line
# through it that is already full. Plateau moves are always accepted.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, lines_through, pts_on) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    lines_through = [[] for _ in range(m)]  # lines containing point P
    pts_on = [[] for _ in range(m)]         # points on line j
    for u, v in edges:
        P, j = u, v - m
        lines_through[P].append(j)
        pts_on[j].append(P)
    return m, edges, lines_through, pts_on


def _arc_search(m, s, lines_through, pts_on, rng, deadline):
    """Return a large set S of point indices with every line holding <= s members of S."""
    inS = [False] * m
    cl = [0] * m
    members = set()

    def add(P):
        inS[P] = True
        members.add(P)
        for j in lines_through[P]:
            cl[j] += 1

    def remove(P):
        inS[P] = False
        members.discard(P)
        for j in lines_through[P]:
            cl[j] -= 1

    order = list(range(m))
    rng.shuffle(order)
    for P in order:
        if all(cl[j] < s for j in lines_through[P]):
            add(P)
    best = list(members)
    T = rng.choice([0.25, 0.35, 0.5])
    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        full = [j for j in lines_through[P] if cl[j] >= s]
        r = len(full)
        delta = 1 - r
        if delta < 0 and rng.random() >= math.exp(delta / T):
            continue
        victims = []
        for j in full:
            cands = [x for x in pts_on[j] if inS[x]]
            victims.append(rng.choice(cands))
        for x in victims:
            remove(x)
        add(P)
        if len(members) > len(best):
            best = list(members)
    return best


def _arc_graph(m, lines_through, pts_on, S):
    """Plane incidence plus one A-vertex per point of S and one B-vertex per line in S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = set()
    for P in range(m):
        for j in lines_through[P]:
            E.add((P, m + j))
    for t, P in enumerate(S):
        a = 2 * m + t
        for j in lines_through[P]:
            E.add((a, m + j))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in pts_on[j]:
            E.add((Q, b))
    return n, sorted(E)


def _saturate(n, edges, m, k, d, rng):
    """Add every missing X-Y edge while both endpoints have spare degree (never lengthens paths)."""
    E = set()
    for u, v in edges:
        E.add((u, v) if u < v else (v, u))
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    X = list(range(m)) + list(range(2 * m, 2 * m + k))
    Y = list(range(m, 2 * m)) + list(range(2 * m + k, 2 * m + 2 * k))
    pairs = [(x, y) for x in X if deg[x] < d for y in Y if deg[y] < d]
    rng.shuffle(pairs)
    for x, y in pairs:
        if deg[x] >= d or deg[y] >= d:
            continue
        key = (x, y) if x < y else (y, x)
        if key in E:
            continue
        E.add(key)
        deg[x] += 1
        deg[y] += 1
    return n, sorted(E)


# ----------------------------------------------------------------------------
# Haar graphs from difference covers (diameter 3 when S - S = Z_m).
# ----------------------------------------------------------------------------

def _cover_search(k, m, rng, deadline):
    """Find S subset of Z_m with |S| = k and S - S = Z_m, or return None."""
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
    """Climb m upward, keeping the largest m with a difference cover. Returns (m, S) or None."""
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
# Generalized quadrangle W(q) (diameter 4), used only for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q); diameter 4."""
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
    budget = 0.8 * float(time_limit)
    deadline = start + budget
    rng = random.Random(seed * 1000003 + 31 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 2:
        # An even cycle of length 2D is bipartite with diameter D: optimal for d = 2.
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D >= 3:
        arc_deadline = start + 0.8 * budget
        qs = sorted((q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)),
                    reverse=True)[:3]
        for idx, q in enumerate(qs):
            now = time.monotonic()
            if now > arc_deadline:
                break
            s = d - q - 1
            m, edges, lt, po = _pg_data(q)
            if s == 0:
                consider(2 * m, edges)
                continue
            remaining = arc_deadline - now
            frac = 0.7 if idx == 0 else 1.0 / (len(qs) - idx)
            slice_end = now + remaining * frac
            S = _arc_search(m, s, lt, po, random.Random(rng.random()), slice_end)
            if S:
                n_c, E_c = _arc_graph(m, lt, po, S)
                n_c, E_c = _saturate(n_c, E_c, m, len(S), d, rng)
                consider(n_c, E_c)

        # Secondary: Haar graph from a difference cover, with the leftover time.
        if time.monotonic() < deadline - 1.0:
            res = _haar_search(d, random.Random(rng.random()), deadline)
            if res is not None:
                m_h, S_h = res
                consider(*lib.haar_graph(m_h, S_h))

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
