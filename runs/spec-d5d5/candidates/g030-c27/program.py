import itertools
import math
import random
import time

import lib

# New idea: multi-fiber ("multi-orbit") voltage lifts over non-abelian groups.
# A base bipartite multigraph with p vertices on each side is lifted over a group G
# of order N, giving 2pN vertices. Every dart (i, j, g) joins fibre A_i to fibre B_j
# with x -> x*g. Left multiplication is an automorphism, so the diameter check only
# needs BFS from one vertex per base vertex. Annealing moves the voltages of the darts.

P_LIST = (2, 3, 1, 4)     # base sizes per side to try
ATTEMPT_BASE = 3.0        # seconds per attempt, grows with repeated failures
WINDOW = 60               # only candidates with order in (floor, floor + WINDOW]
T_HOT = 10.0              # annealing temperature, in unreached-pair units
T_COLD = 0.5
FLOOR_FRAC = 0.35         # start the climb at this fraction of the Moore bound


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
# Multi-fibre group-lift search.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _cost(N, p, D, T, inv, darts):
    """Total number of (source, vertex) pairs at distance > D, over the 2p fibre representatives.

    Vertex (w, x) is stored as w*N + x. Element 0 is the identity.
    A dart (u, j, g) joins (u, x) to (p+j, x*g).
    """
    nb = [[] for _ in range(2 * p)]
    for u, j, g in darts:
        nb[u].append((p + j, g))
        nb[p + j].append((u, inv[g]))
    total = 2 * p * N
    unreached = 0
    for src in range(2 * p):
        seen = bytearray(total)
        s = src * N
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for idx in frontier:
                w, x = divmod(idx, N)
                row = T[x]
                for w2, h in nb[w]:
                    t = w2 * N + row[h]
                    if not seen[t]:
                        seen[t] = 1
                        nxt.append(t)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        unreached += total - count
    return unreached


def _anneal(N, p, d, D, T, inv, rng, end):
    """Anneal the d*p dart voltages to zero unreached pairs. Returns darts or None."""
    darts = []
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        for u in range(p):
            darts.append([u, perm[u], rng.randrange(N)])
    cur = _cost(N, p, D, T, inv, darts)
    t0 = time.monotonic()
    span = max(1e-3, end - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= end:
            return None
        frac = min(1.0, (now - t0) / span)
        temp = T_HOT * (T_COLD / T_HOT) ** frac
        k = rng.randrange(len(darts))
        old = darts[k][2]
        new = rng.randrange(N)
        if new == old:
            continue
        darts[k][2] = new
        v = _cost(N, p, D, T, inv, darts)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[k][2] = old
    return darts


def _attempt(p, N, d, D, rng, end):
    """Try one random group of order N with a p-fibre base. Returns (n, edges) or None."""
    groups = _groups(N)
    m, k, r = rng.choice(groups)
    _, mul, inv_f = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    inv = [inv_f(g) for g in range(N)]
    darts = _anneal(N, p, d, D, T, inv, rng, end)
    if darts is None:
        return None
    return lib.group_lift(2 * p, [(u, p + j, g) for u, j, g in darts], N, mul)


def _search(d, D, rng, deadline, floor):
    """Climb through candidate orders above `floor`; return the largest valid (n, edges) found."""
    moore = lib._moore_bound(d, D)
    tries = {}
    best = None
    while time.monotonic() < deadline:
        cands = []
        for p in P_LIST:
            Nmax = moore // (2 * p)
            lo = max(2, floor // (2 * p) + 1)
            for N in range(lo, Nmax + 1):
                n = 2 * p * N
                if n > floor + WINDOW:
                    break
                cands.append((n, p, N))
        if not cands:
            break
        cands.sort()
        head = cands[:6]
        n, p, N = min(head, key=lambda c: (tries.get((c[1], c[2]), 0), c[0]))
        key = (p, N)
        budget = ATTEMPT_BASE * (1 + 0.5 * tries.get(key, 0))
        end = min(deadline, time.monotonic() + budget)
        try:
            res = _attempt(p, N, d, D, rng, end)
        except Exception:
            res = None
        if res is not None and lib.is_valid(res[0], res[1], d, D):
            best = res
            floor = max(floor, res[0])
        else:
            tries[key] = tries.get(key, 0) + 1
    return best


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

    if d >= 2 and D >= 2 and time.monotonic() < deadline:
        moore = lib._moore_bound(d, D)
        floor = max(best_n, int(FLOOR_FRAC * moore))
        try:
            res = _search(d, D, rng, deadline, floor)
        except Exception:
            res = None
        if res is not None:
            consider(*res)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
