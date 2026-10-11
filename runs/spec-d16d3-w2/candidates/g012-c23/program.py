import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4), kept from the parent.
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
# New construction for D = 3: cyclic Haar graphs from difference covers.
#
# Haar graph H(Z_m, S) with |S| = d has parts A = {a_i}, B = {b_j}, a_i ~ b_{i+s}.
# It is d-regular and bipartite on 2m vertices. Two vertices of the same side are
# at distance 2 exactly when their index difference lies in S - S, and a
# vertex pair across the sides is at distance <= 3 when the difference lies in
# S - S + S. If 0 is in S, S - S + S contains S - S, so it suffices that S - S
# covers all nonzero residues of Z_m. Then diameter <= 3.
# The largest such m is at most d^2 - d + 1 (a perfect difference set would
# give the Moore graph), so we search for covers with m as large as possible.
# ----------------------------------------------------------------------------

def _touch(cnt, unc, x, dl):
    """Change coverage count of residue x by dl (+1 or -1), tracking uncovered count in unc[0]."""
    old = cnt[x]
    new = old + dl
    cnt[x] = new
    if old == 0:
        unc[0] -= 1
    elif new == 0:
        unc[0] += 1


def _cover_search(m, k, rng, deadline):
    """Search S in Z_m with |S| = k, 0 in S, and S - S covering all of Z_m \\ {0}.

    Returns S as a list, or None if the deadline passes first.
    """
    if k < 2 or k > m:
        return None
    S = [0] + rng.sample(range(1, m), k - 1)
    cnt = [0] * m
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    unc = [sum(1 for x in range(1, m) if cnt[x] == 0)]
    inS = [False] * m
    for s in S:
        inS[s] = True
    T = 0.5
    it = 0
    while unc[0] > 0:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            return None
        idx = rng.randrange(1, k)  # S[0] = 0 stays fixed
        s = S[idx]
        r = rng.randrange(1, m)
        if inS[r]:
            continue
        rest = S[:idx] + S[idx + 1:]
        old_unc = unc[0]
        for t in rest:
            _touch(cnt, unc, (s - t) % m, -1)
            _touch(cnt, unc, (t - s) % m, -1)
        for t in rest:
            _touch(cnt, unc, (r - t) % m, 1)
            _touch(cnt, unc, (t - r) % m, 1)
        delta = unc[0] - old_unc
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[idx] = r
            inS[s] = False
            inS[r] = True
        else:
            for t in rest:
                _touch(cnt, unc, (r - t) % m, -1)
                _touch(cnt, unc, (t - r) % m, -1)
            for t in rest:
                _touch(cnt, unc, (s - t) % m, 1)
                _touch(cnt, unc, (t - s) % m, 1)
    return S


def _haar_search(d, D, seed, deadline):
    """Ascend m from a low start, keeping the largest Haar graph whose cover search succeeds."""
    k = d
    rng = random.Random(seed * 1000003 + d * 31 + D)
    best = None
    m = max(k + 1, int(0.68 * (k * (k - 1) + 1)))
    max_m = k * (k - 1) + 1
    fails = 0
    while time.monotonic() < deadline and m <= max_m:
        remaining = deadline - time.monotonic()
        slice_t = min(max(1.0, remaining * 0.3), 10.0)
        S = _cover_search(m, k, rng, min(deadline, time.monotonic() + slice_t))
        if S is not None:
            n, E = lib.haar_graph(m, S)
            if lib.is_valid(n, E, d, D):
                best = (n, E)
            m += 1
            fails = 0
        else:
            fails += 1
            if fails >= 3:
                break
    return best


# ----------------------------------------------------------------------------
# Projective-plane candidate for D >= 3.
# ----------------------------------------------------------------------------

def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (q <= 23)."""
    for q in range(min(d - 1, 23), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best_n, best_E
        if cand is None:
            return
        n, E = cand
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D >= 4 and time.monotonic() < deadline:
        consider(_best_gq(d))

    if D >= 3:
        consider(_pg_best(d))
        if d >= 3 and time.monotonic() < deadline:
            consider(_haar_search(d, D, seed, deadline))

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
