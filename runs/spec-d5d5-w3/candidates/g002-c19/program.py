import itertools
import math
import random
import time

import lib

ITERS = 700            # annealing steps per base/voltage restart
ATTEMPT_BUDGET = 3.0   # seconds per (a, N) attempt
SLACK = 4              # search orders in [lo, lo + SLACK]
A_CHOICES = (2, 3, 4, 1)   # base sizes per side; a > 1 gives non-bi-Cayley lifts


# ----------------------------------------------------------------------------
# Fast fixed constructions (used as safe fallbacks and for special cases).
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
# Voltage-lift search over finite groups with a multi-vertex bipartite base.
#
# Base: a vertices A_0..A_{a-1} and a vertices B_0..B_{a-1}. The base multigraph
# has d darts at each base vertex (sum of d random permutation matrices). Each
# dart (i, j) carries a group element g, giving edges A_{i,x} -- B_{j, x*g}.
# The lift has 2*a*N vertices, is bipartite, and has degree exactly d when the
# darts between the same (i, j) pair carry distinct group elements.
# Left multiplication is an automorphism, so the diameter is the maximum
# eccentricity over the 2a base-vertex representatives.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k (r = 1 is direct)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _random_base(a, d, rng):
    """Random connected base multigraph with degree d at every vertex; return slot list of (i, j) or None."""
    M = [[0] * a for _ in range(a)]
    for _ in range(d):
        p = list(range(a))
        rng.shuffle(p)
        for i in range(a):
            M[i][p[i]] += 1

    parent = list(range(2 * a))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for i in range(a):
        for j in range(a):
            if M[i][j]:
                parent[find(i)] = find(a + j)
    if len({find(x) for x in range(2 * a)}) != 1:
        return None
    slots = []
    for i in range(a):
        for j in range(a):
            slots += [(i, j)] * M[i][j]
    return slots


def _bad(V, adj, D):
    """Number of ordered pairs (v, w) with dist(v, w) > D, via bitmask balls."""
    reach = [1 << v for v in range(V)]
    for _ in range(D):
        new = [0] * V
        for v in range(V):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(V - r.bit_count() for r in reach)


def _cost(a, N, slots, gs, RM, D):
    """Bad-pair count of the lift with the given dart group elements."""
    V = 2 * a * N
    adj = [[] for _ in range(V)]
    for (i, j), g in zip(slots, gs):
        bj = (a + j) * N
        rg = RM[g]
        for x in range(N):
            u = i * N + x
            v = bj + rg[x]
            adj[u].append(v)
            adj[v].append(u)
    return _bad(V, adj, D)


def _anneal(a, N, slots, RM, D, rng, deadline):
    """Anneal dart group elements to zero bad pairs; darts on the same (i, j) keep distinct elements."""
    S = len(slots)
    by = {}
    for s, p in enumerate(slots):
        by.setdefault(p, []).append(s)
    same = [[] for _ in range(S)]
    for idxs in by.values():
        for s in idxs:
            same[s] = [t for t in idxs if t != s]

    gs = [0] * S
    for idxs in by.values():
        vals = rng.sample(range(N), len(idxs))
        for s, v in zip(idxs, vals):
            gs[s] = v

    cur = _cost(a, N, slots, gs, RM, D)
    for it in range(ITERS):
        if cur == 0:
            return gs
        if time.monotonic() > deadline:
            break
        s = rng.randrange(S)
        c = rng.randrange(N)
        if any(gs[t] == c for t in same[s]):
            continue
        old = gs[s]
        gs[s] = c
        v = _cost(a, N, slots, gs, RM, D)
        temp = 1.5 * (1.0 - it / ITERS) + 0.2
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[s] = old
    return gs if cur == 0 else None


def _attempt(a, N, d, D, rng, deadline):
    """Search one random group of order N and random bases until success or deadline.

    Returns (mul, darts) for group_lift, or None.
    """
    groups = _groups(N)
    if not groups or N < d:
        return None
    m, k, r = rng.choice(groups)
    _, mul, _inv = lib.semidirect_group(m, k, r)
    RM = [[mul(x, g) for x in range(N)] for g in range(N)]  # RM[g][x] = x * g
    while time.monotonic() < deadline:
        slots = _random_base(a, d, rng)
        if slots is None:
            continue
        gs = _anneal(a, N, slots, RM, D, rng, deadline)
        if gs is not None:
            return mul, [(i, a + j, g) for (i, j), g in zip(slots, gs)]
    return None


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

    # Record-matching case for D = 3: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    consider(2, [(0, 1)])
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

    if d >= 2 and D >= 2:
        moore = lib._moore_bound(d, D)
        attempt = 0
        budget_scale = 1.0
        while time.monotonic() < deadline:
            any_ok = False
            for _ in range(len(A_CHOICES)):
                if time.monotonic() >= deadline:
                    break
                a = A_CHOICES[attempt % len(A_CHOICES)]
                attempt += 1
                lo = best_n // (2 * a) + 1
                hi = moore // (2 * a)
                if lo > hi:
                    continue
                N = min(hi, lo + rng.randint(0, SLACK))
                if N < d or N < 2:
                    continue
                any_ok = True
                att_deadline = min(deadline, time.monotonic() + ATTEMPT_BUDGET * budget_scale)
                res = _attempt(a, N, d, D, rng, att_deadline)
                if res is not None:
                    mul, darts = res
                    n, e = lib.group_lift(2 * a, darts, N, mul)
                    consider(n, e)
                    budget_scale = 1.0
                else:
                    budget_scale = min(3.0, budget_scale * 1.1)
            if not any_ok:
                break

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
