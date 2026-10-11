import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Cyclic difference-cover search for D = 3 (Haar graphs).
#
# H(m, S) has a_i ~ b_{i+s} for s in S (a Z_m-lift of two vertices joined by
# |S| parallel darts). With |S| <= d it is bipartite with max degree d, and it
# has diameter <= 3 whenever S - S = Z_m: a-a pairs are at distance <= 2 by
# the cover, and a-b pairs are at distance <= 3 because (S - S) + S = Z_m.
# So we search for a d-subset S of Z_m covering all nonzero residues, and
# binary-search the largest feasible m. Order 2m, with m <= d^2 - d + 1.
# ----------------------------------------------------------------------------

def _shift(cnt, m, a, others, sign):
    """Add (sign=+1) or remove (sign=-1) the ordered differences between a and each element
    of `others` in the count table. Returns the change in the number of uncovered residues."""
    dc = 0
    for t in others:
        for z in ((a - t) % m, (t - a) % m):
            if sign < 0:
                cnt[z] -= 1
                if cnt[z] == 0:
                    dc += 1
            else:
                if cnt[z] == 0:
                    dc -= 1
                cnt[z] += 1
    return dc


def _anneal_cover(m, k, rng, deadline):
    """Find a k-subset S of Z_m with S - S = Z_m (every nonzero residue is a difference).
    Returns sorted S, or None if the deadline passes first."""
    if k >= m:
        return list(range(m))
    S = rng.sample(range(m), k)
    inS = [False] * m
    for s in S:
        inS[s] = True
    cnt = [0] * m
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    cost = sum(1 for x in range(1, m) if cnt[x] == 0)
    it = 0
    while cost > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        phase = it % 200000
        T = 0.05 ** (phase / 200000.0)  # geometric cooling 1.0 -> 0.05, then reheat
        i = rng.randrange(k)
        y = rng.randrange(m)
        if inS[y]:
            continue
        old = S[i]
        others = S[:i] + S[i + 1:]
        d1 = _shift(cnt, m, old, others, -1)
        d2 = _shift(cnt, m, y, others, 1)
        delta = d1 + d2
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            inS[old] = False
            inS[y] = True
            cost += delta
        else:
            _shift(cnt, m, y, others, -1)
            _shift(cnt, m, old, others, 1)
    return sorted(S)


def _haar_search(d, rng, start, deadline):
    """Binary-search the largest m in [d, d^2-d+1] with a d-element difference cover of Z_m.
    Returns (m, S). m = d with S = all residues is always feasible."""
    lo, hi = d, d * (d - 1) + 1
    best_S = list(range(d))
    total = deadline - start
    while lo < hi:
        now = time.monotonic()
        if now >= deadline:
            break
        mid = (lo + hi + 1) // 2
        probe = min(deadline - now, max(0.5, total * 0.12))
        S = _anneal_cover(mid, d, rng, now + probe)
        if S is not None:
            lo, best_S = mid, S
        else:
            hi = mid - 1
    return lo, best_S


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (D = 4), kept from the parent.
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
    deadline = start + max(0.5, 0.85 * time_limit - 1.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed * 7919 + d * 131 + D)

    # Safe fallback: K_{d,d} has diameter 2 (valid for any D >= 2).
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, E

    if D == 3:
        # Projective plane incidence graph of PG(2, q), q the largest prime power <= d-1.
        for q in range(min(d - 1, 23), 1, -1):
            if lib.is_prime_power(q):
                n, E = lib.projective_plane_incidence(q)
                consider(n, E)
                break
        # Cyclic Haar graph from a difference cover (the new, higher-risk construction).
        if time.monotonic() < deadline:
            m, S = _haar_search(d, rng, start, deadline)
            n, E = lib.haar_graph(m, S)
            consider(n, E)
    elif D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
