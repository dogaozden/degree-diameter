import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction A (new, primary for D = 3): bi-Cayley / Haar graph over Z_m.
#
# Haar graph H(m, S): a_i ~ b_{i+s} for s in S, |S| = d. Same-side pairs are at
# distance 2 exactly when S - S covers Z_m. So we search for a "difference
# cover" S of size d in Z_m with m as large as possible. Order = 2m.
# The parent's record 394 corresponds to m = 197; a cover with m >= 198 beats it.
# Search: simulated annealing over S with 0 fixed, minimising the number of
# uncovered nonzero residues of S - S.
# ----------------------------------------------------------------------------

def _replace(cnt, S, idx, y, m):
    """Replace S[idx] by y, updating ordered-difference counts cnt.
    Returns the change in the number of uncovered nonzero residues."""
    x = S[idx]
    dz = 0
    for j, o in enumerate(S):
        if j == idx:
            continue
        r = (x - o) % m
        cnt[r] -= 1
        if cnt[r] == 0:
            dz += 1
        r = (o - x) % m
        cnt[r] -= 1
        if cnt[r] == 0:
            dz += 1
    for j, o in enumerate(S):
        if j == idx:
            continue
        r = (y - o) % m
        if cnt[r] == 0:
            dz -= 1
        cnt[r] += 1
        r = (o - y) % m
        if cnt[r] == 0:
            dz -= 1
        cnt[r] += 1
    S[idx] = y
    return dz


def _cover_sa(m, k, rng, deadline):
    """Find S (|S| = k, 0 in S, distinct mod m) with S - S = Z_m, or return None at deadline."""
    S = [0] + rng.sample(range(1, m), k - 1)
    cnt = [0] * m
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    unc = sum(1 for r in range(1, m) if cnt[r] == 0)
    T = 0.5
    steps = 0
    while unc > 0:
        steps += 1
        if steps & 255 == 0 and time.monotonic() > deadline:
            return None
        idx = rng.randrange(1, k)
        y = rng.randrange(1, m)
        if y in S:
            continue
        x = S[idx]
        dz = _replace(cnt, S, idx, y, m)
        if dz <= 0 or rng.random() < math.exp(-dz / T):
            unc += dz
        else:
            _replace(cnt, S, idx, x, m)
    return S


def _haar_search(k, rng, deadline, slice_s=5.0):
    """Climb m upward from k+1, finding a difference cover of size k in Z_m at each step.
    Returns the list of successful (m, S) pairs."""
    found = []
    m = k + 1
    cap = k * (k - 1) + 1  # ordered differences must cover m - 1 residues
    while m <= cap:
        S = None
        while S is None:
            now = time.monotonic()
            if now >= deadline:
                return found
            S = _cover_sa(m, k, rng, min(deadline, now + slice_s))
        found.append((m, S))
        m += 1
    return found


# ----------------------------------------------------------------------------
# Construction B (fallback for D = 3): PG(2,q) plus arc-extension vertices.
# ----------------------------------------------------------------------------

def _pg_incidence(q):
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
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


def _arc_graph(m, edges, point_lines, line_points, S):
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in point_lines[P]:
            E.append((a, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_candidates(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points = _pg_incidence(q)
        index = {p: i for i, p in enumerate(lib.projective_points(q))}
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 60, deadline))
        if s >= 2:
            cs = _conic_set(q, index)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) baseline for D >= 4 (unchanged from parent).
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
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)
            return True
        return False

    if D == 3:
        # Arc-extended PG(2,q) graphs (cheap, small time slice).
        cands = _arc_candidates(d, start + 0.15 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c in cands:
            consider(n_c, E_c)

        # Main new construction: bi-Cayley Haar graph over Z_m with a difference cover.
        if d >= 2:
            found = _haar_search(d, rng, deadline)
            for m, S in reversed(found):
                if 2 * m <= best_n:
                    break
                E = lib.haar_graph(m, S)[1]
                if consider(2 * m, E):
                    break

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
