import itertools
import math
import random
import time

import lib

GROUPS_PER_CONFIG = 6      # groups tried per (k, M) configuration in one round
_GROUP_CACHE = {}
_GROUPS_OF = {}


# ----------------------------------------------------------------------------
# Safe baseline families (always checked with lib.is_valid before use).
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Voltage lifts over small bipartite base multigraphs with k vertices per side
# and a finite group G of order M (non-cyclic groups included).
#
# Base A-vertices 0..k-1, B-vertices k..2k-1. Each dart (u, v, g) joins
# (u, x) to (v, x*g). Left multiplication is an automorphism, so eccentricities
# from (u, 1) for each of the 2k base vertices decide the diameter.
# The base is d-regular on both sides: exactly d darts leave each A-vertex and
# enter each B-vertex. Moves: relabel a dart, or swap endpoints of two darts
# (both keep the degrees fixed). Cost = number of (source, vertex) pairs
# farther than D.
# ----------------------------------------------------------------------------

def _groups_of(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k (cached)."""
    if N not in _GROUPS_OF:
        out = []
        for k in range(1, N + 1):
            if N % k:
                continue
            m = N // k
            for r in range(m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    out.append((m, k, r))
        _GROUPS_OF[N] = out
    return _GROUPS_OF[N]


def _group(m, k, r):
    """(order, multiplication table T with T[x][g] = x*g, mul, inverse list)."""
    key = (m, k, r)
    if key not in _GROUP_CACHE:
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(order)] for x in range(order)]
        invs = [inv(g) for g in range(order)]
        _GROUP_CACHE[key] = (order, T, mul, invs)
    return _GROUP_CACHE[key]


def _nbrs(k, darts, invs):
    """Neighbour lists on the base: (other base index, right-multiplier)."""
    nb = [[] for _ in range(2 * k)]
    for u, v, g in darts:
        nb[u].append((k + v, g))
        nb[k + v].append((u, invs[g]))
    return nb


def _cost(k, M, T, nb, D):
    """Total number of (source, vertex) pairs not within distance D, sources (b, identity)."""
    N = 2 * k * M
    total = 0
    for sb in range(2 * k):
        s = sb * M
        seen = bytearray(N)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for vert in frontier:
                b = vert // M
                row = T[vert - b * M]
                for w, h in nb[b]:
                    idx = w * M + row[h]
                    if not seen[idx]:
                        seen[idx] = 1
                        nxt.append(idx)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
    return total


def _anneal(k, d, M, T, invs, D, rng, iters, deadline):
    """Anneal a d-regular base multigraph with labels in G until every pair is within D."""
    A = [u for u in range(k) for _ in range(d)]
    B = [v for v in range(k) for _ in range(d)]
    rng.shuffle(B)
    darts = []
    keys = set()
    for u, v in zip(A, B):
        g = None
        for _ in range(64):
            c = rng.randrange(M)
            if (u, v, c) not in keys:
                g = c
                break
        if g is None:
            return None
        keys.add((u, v, g))
        darts.append((u, v, g))

    cur = _cost(k, M, T, _nbrs(k, darts, invs), D)
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() >= deadline:
            break
        temp = max(0.2, 3.0 * (1.0 - it / iters))
        i = rng.randrange(len(darts))
        ui, vi, gi = darts[i]
        if k > 1 and rng.random() < 0.5:
            j = rng.randrange(len(darts))
            if j == i:
                continue
            uj, vj, gj = darts[j]
            n1 = (ui, vj, gi)
            n2 = (uj, vi, gj)
            if n1 == n2 or n1 in keys or n2 in keys:
                continue
            old_i, old_j = darts[i], darts[j]
            darts[i], darts[j] = n1, n2
            keys.discard(old_i)
            keys.discard(old_j)
            keys.add(n1)
            keys.add(n2)
            new = _cost(k, M, T, _nbrs(k, darts, invs), D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                cur = new
            else:
                darts[i], darts[j] = old_i, old_j
                keys.discard(n1)
                keys.discard(n2)
                keys.add(old_i)
                keys.add(old_j)
        else:
            g2 = rng.randrange(M)
            if g2 == gi:
                continue
            n1 = (ui, vi, g2)
            if n1 in keys:
                continue
            darts[i] = n1
            keys.discard((ui, vi, gi))
            keys.add(n1)
            new = _cost(k, M, T, _nbrs(k, darts, invs), D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                cur = new
            else:
                darts[i] = (ui, vi, gi)
                keys.discard(n1)
                keys.add((ui, vi, gi))
    return darts if cur == 0 else None


def _attempt(d, D, total, rng, deadline):
    """Search (k, M, group) configurations with 2*k*M = total; return a valid (n, edges) or None."""
    configs = []
    for k in range(1, total // 2 + 1):
        if total % (2 * k):
            continue
        M = total // (2 * k)
        if M >= 2:
            configs.append((k, M))
    if not configs:
        return None
    iters = 400
    while time.monotonic() < deadline:
        rng.shuffle(configs)
        for k, M in configs:
            groups = list(_groups_of(M))
            rng.shuffle(groups)
            for m, kk, r in groups[:GROUPS_PER_CONFIG]:
                if time.monotonic() >= deadline:
                    return None
                _, T, mul, invs = _group(m, kk, r)
                darts = _anneal(k, d, M, T, invs, D, rng, iters, deadline)
                if darts is not None:
                    offs = [(u, k + v, g) for (u, v, g) in darts]
                    n, edges = lib.group_lift(2 * k, offs, M, mul)
                    if lib.is_valid(n, edges, d, D):
                        return n, edges
        iters = min(iters * 2, 40000)
    return None


def _search(d, D, start, cap, rng, deadline, consider):
    """Bisection-style search over even totals; keeps the largest total that succeeds."""
    lo = None
    hi = None
    T = start
    for _ in range(14):
        if time.monotonic() >= deadline or T > cap or T < 4:
            break
        if lo is not None and hi is not None and hi - lo <= 2:
            break
        now = time.monotonic()
        level_dl = min(deadline, now + max(1.0, 0.5 * (deadline - now)))
        res = _attempt(d, D, T, rng, level_dl)
        if res is not None:
            consider(*res)
            if lo is None or T > lo:
                lo = T
            if hi is None:
                T = lo + 8
            else:
                mid = ((lo + hi) // 4) * 2
                if mid <= lo:
                    mid = lo + 2
                if mid >= hi:
                    break
                T = mid
        else:
            if hi is None or T < hi:
                hi = T
            if lo is None:
                T = hi - 16
            else:
                mid = ((lo + hi) // 4) * 2
                if mid <= lo:
                    mid = lo + 2
                if mid >= hi:
                    break
                T = mid


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 6.0))
    deadline = t0 + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed)
    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0] = n
            best[1] = e

    # Record-matching case for D = 3: incidence graph of PG(2, d-1).
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

    # Safe fallbacks.
    consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Lift search over non-cyclic groups.
    if d >= 2 and D >= 2 and time.monotonic() < deadline:
        start = 338 if (d == 5 and D == 5) else max(4, 2 * d)
        cap = lib._moore_bound(d, D)
        _search(d, D, start, cap, rng, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
