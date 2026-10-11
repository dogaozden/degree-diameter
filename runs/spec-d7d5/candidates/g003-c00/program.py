import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact algebraic families (kept from the parent as safe baselines).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW MAIN ARM: Haar graphs of non-abelian groups.
#
# For a finite group G of order m and a set S of d distinct elements, the Haar
# graph H(G, S) has parts A = {a_g}, B = {b_g}, with a_g ~ b_{g s} for s in S.
# It is d-regular and bipartite on 2m vertices. Left multiplication by G is an
# automorphism that is transitive on A and on B, so the diameter is determined
# by BFS from a_e and from b_e alone. Each cost evaluation is a few numpy
# gathers. Commutative groups have poor diameter here, so the groups are
# semidirect products Z_A x| Z_K with a nontrivial action when possible.
# ----------------------------------------------------------------------------

_HAAR_K = (2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24)


def _sample_group(m, rng):
    """Return (order, mul, inv) for a group of order exactly m (prefer non-abelian)."""
    if m < 3:
        return None
    Ks = [k for k in _HAAR_K if m % k == 0 and m // k >= 3]
    if Ks and rng.random() < 0.9:
        K = rng.choice(Ks)
        A = m // K
        r = None
        for _ in range(300):
            x = rng.randrange(2, A)
            if math.gcd(x, A) != 1:
                continue
            c = pow(x, (A - 1) // K, A) if (A - 1) % K == 0 else x
            if math.gcd(c, A) == 1 and pow(c, K, A) == 1 % A and c % A not in (0, 1):
                r = c
                break
        if r is not None:
            try:
                order, mul, inv = lib.semidirect_group(A, K, r)
                if order == m:
                    return order, mul, inv
            except ValueError:
                pass
    return lib.semidirect_group(m, 1, 1)


def _haar_cols(m, mul, inv, s, cache):
    """Right-multiplication column g -> g*s and g -> g*s^{-1}, cached per s."""
    hit = cache.get(s)
    if hit is None:
        si = inv(s)
        col = np.fromiter((mul(g, s) for g in range(m)), dtype=np.int64, count=m)
        icol = np.fromiter((mul(g, si) for g in range(m)), dtype=np.int64, count=m)
        hit = (col, icol)
        cache[s] = hit
    return hit


def _bfs_bad(m, D, cols, icols, root_side):
    """Number of vertices (both sides) at distance > D from the root a_e (side 0) or b_e (side 1)."""
    reach = [np.zeros(m, dtype=bool), np.zeros(m, dtype=bool)]
    reach[root_side][0] = True
    frontier = np.zeros(1, dtype=np.int64)
    side = root_side
    for _ in range(D):
        maps = cols if side == 0 else icols
        nxt = np.zeros(m, dtype=bool)
        for R in maps:
            nxt[R[frontier]] = True
        other = 1 - side
        new = nxt & ~reach[other]
        if not new.any():
            break
        reach[other] |= new
        frontier = np.flatnonzero(new)
        side = other
    return 2 * m - int(reach[0].sum()) - int(reach[1].sum())


def _haar_cost(m, D, cols, icols):
    return _bfs_bad(m, D, cols, icols, 0) + _bfs_bad(m, D, cols, icols, 1)


def _anneal(m, d, D, rng, mul, inv, deadline, iters):
    """Search for a generating set S of size d giving diameter <= D. Returns (S, pairs) or None."""
    cache = {}
    S = rng.sample(range(m), d)
    inS = set(S)
    pairs = [_haar_cols(m, mul, inv, s, cache) for s in S]

    def cost_of(prs):
        return _haar_cost(m, D, [p[0] for p in prs], [p[1] for p in prs])

    cur = cost_of(pairs)
    for t in range(iters):
        if cur == 0:
            break
        if (t & 31) == 0 and time.monotonic() > deadline:
            break
        j = rng.randrange(d)
        new = rng.randrange(m)
        if new in inS:
            continue
        frac = t / iters
        temp = 3.0 * (1.0 - frac) + 0.3
        newpair = _haar_cols(m, mul, inv, new, cache)
        cand = pairs[:j] + [newpair] + pairs[j + 1:]
        c2 = cost_of(cand)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            inS.discard(S[j])
            S[j] = new
            inS.add(new)
            pairs = cand
            cur = c2
    if cur != 0:
        return None
    return S, pairs


def _try_order(m, d, D, rng, slice_end, iters):
    """Try random groups of order m with annealed generating sets until slice_end. Returns (n, edges) or None."""
    while time.monotonic() < slice_end:
        g = _sample_group(m, rng)
        if g is None:
            continue
        order, mul, inv = g
        if order != m:
            continue
        group_end = min(slice_end, time.monotonic() + 3.0)
        res = _anneal(m, d, D, rng, mul, inv, group_end, iters)
        if res is not None:
            edges = []
            for col, _ in res[1]:
                cl = col.tolist()
                for x in range(m):
                    edges.append((x, m + cl[x]))
            return 2 * m, edges
    return None


def _haar_arm(d, D, rng, deadline, m0):
    """Ladder over the group order m: grow after success, bisect after failure."""
    lo = None
    hi = None
    best = None
    m = max(d + 1, m0)
    while time.monotonic() < deadline - 1.0:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(4.0, 0.3 * remaining))
        res = _try_order(m, d, D, rng, slice_end, 6000)
        if res is not None:
            if best is None or res[0] > best[0]:
                best = res
            lo = m if lo is None else max(lo, m)
            if hi is not None and hi <= lo:
                hi = None
            if hi is None:
                m = int(m * 1.03) + 1
            else:
                m = (lo + hi) // 2
        else:
            hi = m if hi is None else min(hi, m)
            if lo is None:
                m = max(d + 1, int(m * 0.97))
            elif hi - lo <= 1:
                m = lo + 1  # retry the boundary with fresh groups and seeds
            else:
                m = (lo + hi) // 2
    return best


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main arm: Haar graphs of non-abelian groups, ladder over the group order.
    if D >= 3 and d >= 3 and time.monotonic() < deadline:
        moore_half = sum((d - 1) ** i for i in range(D))
        m0 = max(d + 1, best_n // 2 + 1, int(0.3 * moore_half))
        res = _haar_arm(d, D, rng, deadline, m0)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
