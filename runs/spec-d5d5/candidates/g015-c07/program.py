import itertools
import math
import random
import time

import lib

# Search knobs.
MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per (base size, order) attempt
ITERS = 400                   # annealing steps per (group, base) try
MAX_ORDER = 1200              # never search for graphs with more vertices than this
MAX_N = 320                   # cap on group order (keeps multiplication tables small)
BASE_SIZES = (1, 2, 3)        # vertices per side of the voltage base multigraph

# Idea (new in this version): multi-vertex base voltage lifts.
# The base is a b+b bipartite multigraph with every vertex of degree d. It is drawn
# as a sum of d random permutation matrices, so each row and column sums to d.
# Each base dart (u, v) carries a group voltage g, and the lift joins
# A(u, x) to B(v, x*g) for all x in G. The lift has 2*b*N vertices and degree d.
# Left multiplication by h is an automorphism of the lift, so each fiber is
# transitive, and the diameter check needs BFS from only 2*b sources. The
# annealing moves individual voltages within each base cell. b = 1 recovers the
# bi-Cayley search; b = 2, 3 give orders 4N and 6N for the same group size N.


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Groups Z_m x|_r Z_k of order N, with cached multiplication and inverse tables.
# ----------------------------------------------------------------------------

_TABLE_CACHE = {}


def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for gk in range(1, N + 1):
        if N % gk:
            continue
        gm = N // gk
        for gr in range(gm):
            if math.gcd(gr, gm) == 1 and pow(gr, gk, gm) == 1 % gm:
                out.append((gm, gk, gr))
    return out


def _tables(N, gm, gk, gr):
    """Return (T, invs): T[x][g] = x*g and invs[g] = g^{-1} for the group, cached per parameters."""
    key = (gm, gk, gr)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    _, mul, inv = lib.semidirect_group(gm, gk, gr)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    _TABLE_CACHE[key] = (T, invs)
    return T, invs


# ----------------------------------------------------------------------------
# Base multigraphs and voltage lifts.
# ----------------------------------------------------------------------------

def _base_connected(b, M):
    """True if the bipartite base multigraph with multiplicities M (b x b) is connected."""
    seen = [False] * (2 * b)
    seen[0] = True
    stack = [0]
    while stack:
        w = stack.pop()
        if w < b:
            nbrs = [b + v for v in range(b) if M[w][v]]
        else:
            v = w - b
            nbrs = [u for u in range(b) if M[u][v]]
        for z in nbrs:
            if not seen[z]:
                seen[z] = True
                stack.append(z)
    return all(seen)


def _random_base(b, d, rng):
    """Random connected b+b multigraph with all degrees d, as a sum of d permutation matrices."""
    while True:
        M = [[0] * b for _ in range(b)]
        for _ in range(d):
            perm = list(range(b))
            rng.shuffle(perm)
            for u in range(b):
                M[u][perm[u]] += 1
        if _base_connected(b, M):
            return M


def _unreached(N, b, T, invs, darts, D):
    """Count (source, vertex) pairs at distance > D, over the 2*b fiber sources.

    The lift has parts A (indices u*N + x) and B (indices b*N + v*N + y).
    Dart (u, v, g) joins A(u, x) to B(v, x*g).
    """
    n_tot = 2 * b * N
    base_B = b * N
    fromA = [[] for _ in range(b)]   # fromA[u] = [(v, g)]
    fromB = [[] for _ in range(b)]   # fromB[v] = [(u, g^{-1})]
    for u, v, g in darts:
        fromA[u].append((v, g))
        fromB[v].append((u, invs[g]))
    sources = [u * N for u in range(b)] + [base_B + v * N for v in range(b)]
    total = 0
    for src in sources:
        seen = bytearray(n_tot)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for w in frontier:
                if w < base_B:
                    u, x = divmod(w, N)
                    row = T[x]
                    for v, g in fromA[u]:
                        z = base_B + v * N + row[g]
                        if not seen[z]:
                            seen[z] = 1
                            nxt.append(z)
                else:
                    v, y = divmod(w - base_B, N)
                    row = T[y]
                    for u, hi in fromB[v]:
                        z = u * N + row[hi]
                        if not seen[z]:
                            seen[z] = 1
                            nxt.append(z)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += n_tot - count
    return total


def _anneal_lift(N, b, T, invs, M, D, rng, iters, deadline):
    """Anneal the voltages inside each base cell to zero unreached pairs; return darts or None."""
    cells = [(u, v) for u in range(b) for v in range(b) if M[u][v] > 0]
    # Within a cell, voltages are distinct so no duplicate edges arise.
    vol = {c: rng.sample(range(N), M[c[0]][c[1]]) for c in cells}

    def darts_of():
        return [(u, v, g) for (u, v) in cells for g in vol[(u, v)]]

    cur = _unreached(N, b, T, invs, darts_of(), D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        cell = cells[rng.randrange(len(cells))]
        lst = vol[cell]
        i = rng.randrange(len(lst))
        c = rng.randrange(N)
        if c in lst:
            continue
        old = lst[i]
        lst[i] = c
        val = _unreached(N, b, T, invs, darts_of(), D)
        if val <= cur or rng.random() < math.exp(-(val - cur) / temp):
            cur = val
        else:
            lst[i] = old
    if cur == 0:
        return darts_of()
    return None


def _attempt_lift(N, b, d, D, rng, deadline):
    """Try groups of order N (with a random base of b vertices per side) until one lift works."""
    groups = _groups(N)
    rng.shuffle(groups)
    for gm, gk, gr in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        T, invs = _tables(N, gm, gk, gr)
        M = _random_base(b, d, rng)
        darts = _anneal_lift(N, b, T, invs, M, D, rng, ITERS, deadline)
        if darts is not None:
            return T, darts
    return None


def _lift_edges(N, b, T, darts):
    """Expand darts into the explicit edge list of the lift."""
    off = b * N
    edges = []
    for u, v, g in darts:
        for x in range(N):
            edges.append((u * N + x, off + v * N + T[x][g]))
    return 2 * b * N, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    cap = min(moore, MAX_ORDER)

    budget = 0.5
    while time.monotonic() < deadline:
        # Candidate (order, base size, group order) triples above the current best,
        # smallest first: the cheapest improvements are tried before larger ones.
        cands = []
        for b in BASE_SIZES:
            lo = max(d, best_n // (2 * b) + 1)
            hi = min(MAX_N, cap // (2 * b))
            for N in range(lo, hi + 1):
                size = 2 * b * N
                if best_n < size <= cap:
                    cands.append((size, b, N))
        if not cands:
            break
        cands.sort()

        any_success = False
        for size, b, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            if size <= best_n:
                continue
            att_deadline = min(deadline, now + budget)
            res = _attempt_lift(N, b, d, D, rng, att_deadline)
            if res is None:
                continue
            T, darts = res
            n, edges = _lift_edges(N, b, T, darts)
            consider(n, edges)
            any_success = True

        if not any_success:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
