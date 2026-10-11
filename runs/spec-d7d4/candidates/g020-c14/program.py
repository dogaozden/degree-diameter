import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured base graphs (used when they meet the Moore bound or are cheap).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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


# ----------------------------------------------------------------------------
# Cyclic Haar graphs H(m, S): a_i ~ b_{i+s} for s in S (bipartite, d-regular).
# H is vertex-transitive on each side under rotation, so the diameter equals the
# larger eccentricity of a_0 and b_0. The cost below counts vertices NOT within
# distance D of a_0 plus those not within distance D of b_0.
# ----------------------------------------------------------------------------

def _cost(m, S, D):
    total = 0
    for start in (0, m):
        seen = bytearray(2 * m)
        seen[start] = 1
        frontier = [start]
        cnt = 1
        for _ in range(D):
            nxt = []
            for x in frontier:
                if x < m:
                    i = x
                    for s in S:
                        y = m + (i + s) % m
                        if not seen[y]:
                            seen[y] = 1
                            nxt.append(y)
                            cnt += 1
                else:
                    j = x - m
                    for s in S:
                        y = (j - s) % m
                        if not seen[y]:
                            seen[y] = 1
                            nxt.append(y)
                            cnt += 1
            frontier = nxt
            if not frontier:
                break
        total += 2 * m - cnt
    return total


def _climb(m, d, D, end, rng):
    """Hill-climb a connection set S of size d (containing 0) with zero cost, or return None."""
    if m - 1 == d - 1:
        return list(range(m))
    S = [0] + rng.sample(range(1, m), d - 1)
    c = _cost(m, S, D)
    while c > 0 and time.monotonic() < end:
        k = rng.randrange(1, d)
        new = rng.randrange(1, m)
        if new in S:
            continue
        old = S[k]
        S[k] = new
        c2 = _cost(m, S, D)
        if c2 <= c or rng.random() < 0.02:
            c = c2
        else:
            S[k] = old
    return list(S) if c == 0 else None


def _haar_search(d, D, deadline, rng):
    """Search for the largest m with a valid cyclic Haar graph H(m, S), |S| = d."""
    if d < 2:
        return None
    mmax = lib._moore_bound(d, D) // 2
    if mmax < d:
        return None

    def attempt(m, sl):
        return _climb(m, d, D, min(deadline, time.monotonic() + sl), rng)

    # Coarse descent from the Moore-type bound until something works.
    m = mmax
    found = None
    while m >= d and time.monotonic() < deadline:
        S = attempt(m, 0.3)
        if S is not None:
            found = (m, S)
            break
        m -= max(1, m // 40)
    if found is None:
        return None

    # Refine upward with growing time slices.
    bm, bS = found
    fails = 0
    while time.monotonic() < deadline:
        m = bm + 1
        if m > mmax:
            break
        S = attempt(m, 1.0 * (1.5 ** min(fails, 12)))
        if S is not None:
            bm, bS = m, S
            fails = 0
        else:
            fails += 1
    return bm, bS


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured candidates where they exist.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
    if D == 4 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 9:
        consider(*_gq_w(d - 1))

    # Already at the Moore bound: nothing to gain.
    if best[0] >= lib._moore_bound(d, D):
        return best

    # Main construction: cyclic Haar graphs found by hill-climbing on the connection set.
    res = _haar_search(d, D, deadline, rng)
    if res is not None:
        m, S = res
        n, e = lib.haar_graph(m, S)
        consider(n, e)

    return best
