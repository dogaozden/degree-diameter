import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe base graphs: projective planes (D = 3) and generalized quadrangles W(q) (D = 4).
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


def _largest_pp_at_most(limit):
    for q in range(limit, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


# ----------------------------------------------------------------------------
# NEW construction: bipartite voltage lifts over small (possibly non-cyclic) groups.
#
# Base graph: a A-vertices and a B-vertices, d-regular multigraph with voltages
# in a group G of order N. The lift has 2aN vertices and max degree d, and is
# bipartite by construction. Left multiplication by a group element is an
# automorphism of the lift, so diameter is checked by BFS from one root per
# base vertex only. Hill climbing over voltages and B-endpoints drives the
# number of unreached (vertex, root) pairs to zero. Order N is found by
# binary search per base size a.
# ----------------------------------------------------------------------------

def _random_group(N, rng):
    """Random group of order N: cyclic, or a semidirect product Z_m x| Z_k. Returns (T, ginv, mul)."""
    cands = [None]
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append((m, k, r))
    pick = rng.choice(cands)
    if pick is None:
        _, mul, inv = lib.cyclic_group(N)
    else:
        _, mul, inv = lib.semidirect_group(*pick)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    ginv = [inv(g) for g in range(N)]
    return T, ginv, mul


def _init(a, N, d, rng):
    """Random d-regular base darts (A index, B index, voltage)."""
    if a == 1:
        vols = rng.sample(range(N), d) if N >= d else [rng.randrange(N) for _ in range(d)]
        return [(0, 0, g) for g in vols]
    As = [i for i in range(a) for _ in range(d)]
    Bs = As[:]
    rng.shuffle(Bs)
    return [(i, j, rng.randrange(N)) for i, j in zip(As, Bs)]


def _score(a, N, T, ginv, darts, D):
    """Number of (root, vertex) pairs at distance > D, over roots (base vertex, identity)."""
    total = 2 * a * N
    nbA = [[] for _ in range(a)]
    nbB = [[] for _ in range(a)]
    for i, j, g in darts:
        nbA[i].append((a + j, g))
        nbB[j].append((i, g))
    bad = 0
    for root_w in range(2 * a):
        seen = bytearray(total)
        seen[root_w * N] = 1
        frontier = [(root_w, 0)]
        reached = 1
        for _ in range(D):
            nxt = []
            for w, x in frontier:
                if w < a:
                    for w2, g in nbA[w]:
                        x2 = T[x][g]
                        idx = w2 * N + x2
                        if not seen[idx]:
                            seen[idx] = 1
                            nxt.append((w2, x2))
                else:
                    for w2, g in nbB[w - a]:
                        x2 = T[x][ginv[g]]
                        idx = w2 * N + x2
                        if not seen[idx]:
                            seen[idx] = 1
                            nxt.append((w2, x2))
            reached += len(nxt)
            frontier = nxt
            if not frontier:
                break
        bad += total - reached
    return bad


def _probe(a, N, d, D, rng, t_end):
    """Try to find a valid lift of order 2aN by restarted hill climbing. Returns (darts, mul) or None."""
    while time.monotonic() < t_end:
        T, ginv, mul = _random_group(N, rng)
        darts = _init(a, N, d, rng)
        cur = _score(a, N, T, ginv, darts, D)
        steps = 0
        while cur and steps < 500 and time.monotonic() < t_end:
            steps += 1
            new = list(darts)
            k = rng.randrange(len(new))
            if rng.random() < 0.7:
                i, j, _ = new[k]
                new[k] = (i, j, rng.randrange(N))
            else:
                k2 = rng.randrange(len(new))
                i1, j1, g1 = new[k]
                i2, j2, g2 = new[k2]
                if j1 == j2:
                    continue
                new[k] = (i1, j2, g1)
                new[k2] = (i2, j1, g2)
            s = _score(a, N, T, ginv, new, D)
            if s <= cur:
                darts, cur = new, s
        if cur == 0:
            return darts, mul
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if best[0] >= lib._moore_bound(d, D):
        return best

    # Known-construction base graphs (safe, verified).
    if D == 3:
        q = _largest_pp_at_most(d - 1)
        if q:
            consider(*lib.projective_plane_incidence(q))
    elif D == 4:
        q = _largest_pp_at_most(min(d - 1, 11))
        if q:
            consider(*_gq_w(q))

    # Main search: voltage lifts over small groups, binary search on group order.
    Moore = lib._moore_bound(d, D)
    ends = {1: start + 0.35 * time_limit,
            2: start + 0.60 * time_limit,
            3: start + 0.78 * time_limit}
    for a in (1, 2, 3):
        end = ends[a]
        lo, hi = 1, Moore // (2 * a)
        cap = 2.5 if a == 1 else 3.0
        while lo < hi and time.monotonic() < end - 0.5:
            mid = (lo + hi + 1) // 2
            t_end = min(end, time.monotonic() + cap)
            r = _probe(a, mid, d, D, rng, t_end)
            if r is None:
                hi = mid - 1
            else:
                darts, mul = r
                base_darts = [(i, a + j, g) for i, j, g in darts]
                _, e = lib.group_lift(2 * a, base_darts, mid, mul)
                consider(2 * a * mid, e)
                lo = mid

    return best
