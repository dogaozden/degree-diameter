import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Known algebraic constructions (kept as candidates; they are cheap).
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _ara(d):
    """Araujo-Pardo & Lopez graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


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
    """W(q) for the largest small prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New main family for diameter 3: cyclic Haar graphs from difference covers.
#
# Haar graph H(m, S): A_i ~ B_j iff j - i in S, with S a d-subset of Z_m.
# It is bipartite and d-regular. Its diameter is at most 3 iff S - S = Z_m:
#   * A-A and B-B pairs at distance <= 2 need every x in Z_m to be a difference,
#   * A-B pairs then reach distance <= 3 automatically, since S - S + S = Z_m.
# So the task is to find a d-subset of Z_m whose difference set covers Z_m,
# with m as large as possible. Search by simulated annealing on the number of
# uncovered nonzero residues, which is cheap to update incrementally.
# ----------------------------------------------------------------------------

def _shift(counts, m, others, v, sign):
    """Add sign to the ordered-difference counts of v against each element of others.

    Returns the change in the number of zero entries among counts[1..m-1].
    """
    dz = 0
    for t in others:
        for x in ((v - t) % m, (t - v) % m):
            c = counts[x] + sign
            counts[x] = c
            if sign < 0:
                if c == 0:
                    dz += 1
            elif c == 1:
                dz -= 1
    return dz


def _diff_cover_search(d, m, rng, deadline, iters):
    """Anneal a d-subset S of Z_m (containing 0) with S - S = Z_m. Returns S or None."""
    if d < 2 or m < d:
        return None
    counts = [0] * m
    S = [0] + rng.sample(range(1, m), d - 1)
    inS = [False] * m
    for s in S:
        inS[s] = True
    for a in range(d):
        for b in range(d):
            if a != b:
                counts[(S[a] - S[b]) % m] += 1
    zeros = sum(1 for x in range(1, m) if counts[x] == 0)

    T0, T1 = 1.0, 0.02
    for it in range(iters):
        if zeros == 0:
            return list(S)
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        new = rng.randrange(1, m)
        if inS[new]:
            continue
        old = S[i]
        others = S[:i] + S[i + 1:]
        T = T0 * (T1 / T0) ** (it / iters)
        dz = _shift(counts, m, others, old, -1) + _shift(counts, m, others, new, 1)
        if dz <= 0 or rng.random() < math.exp(-dz / T):
            zeros += dz
            inS[old] = False
            inS[new] = True
            S[i] = new
        else:
            _shift(counts, m, others, new, -1)
            _shift(counts, m, others, old, 1)
    return list(S) if zeros == 0 else None


def _haar_search_d3(d, deadline, rng):
    """Climb m upward while difference covers are found; return (m, S) for the largest m found."""
    best = None
    m = max(d, int(0.8 * (d * d - d + 1)))
    fails = 0
    while time.monotonic() < deadline and m <= d * d - d + 1:
        S = None
        for _ in range(2):
            if time.monotonic() >= deadline:
                break
            S = _diff_cover_search(d, m, rng, deadline, 80000)
            if S is not None:
                break
        if S is not None:
            best = (m, S)
            m += 1
            fails = 0
        else:
            fails += 1
            if fails >= 3:
                break
            m += 1
    return best


# ----------------------------------------------------------------------------
# Generic Haar hill-climb for diameter >= 4 (secondary family).
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m for diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Algebraic candidates (cheap, computed first).
        ara = _ara(d)
        if ara is not None:
            consider(ara[0], ara[1])
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D == 3:
        # Main new family: cyclic Haar graphs H(m, S) with S - S = Z_m.
        # Only uses the time left after the cheap candidates above.
        res = _haar_search_d3(d, deadline, rng)
        if res is not None:
            m, S = res
            consider(*lib.haar_graph(m, S))

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
        m = d + 1
        cap = 4 * d * d + 10
        while m <= cap and time.monotonic() < deadline:
            S = _search_haar(d, D, m, rng, deadline, 120)
            if S is not None:
                consider(*lib.haar_graph(m, S))
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
