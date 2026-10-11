import itertools
import math
import random
import time

import lib

ITERS = 1500          # annealing proposals per (t, N, group) attempt
ATTEMPT_CAP = 3.0     # seconds per attempt before moving to another group
SPAN = 10             # orders tried above the current lower bound


# ----------------------------------------------------------------------------
# Baseline families (fast, validated before use).
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
# Multi-base voltage lifts over semidirect groups.
#
# Base: t vertices A_0..A_{t-1} and t vertices B_0..B_{t-1}. Layer l (of d layers)
# joins A_i to B_{P[l][i]}, where P[0] is the identity and P[l] is a permutation.
# Dart (l, i) has voltage V[l][i] in G, giving the lift edges
#     A_i x -- B_{P[l][i]} (x * V[l][i])   for all x in G.
# Every vertex has degree exactly d. Left multiplication by G is an automorphism,
# so distances from the fiber representatives A_i*e and B_j*e decide the diameter:
# only 2t BFS runs are needed per evaluation. Voltages for darts from A_i to the
# same B_j are kept distinct, which makes the lift simple.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k (k = 1 is cyclic)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _ok(V, P, l, i, g, d):
    """True if voltage g for dart (l, i) keeps darts from A_i to the same B_j distinct."""
    j = P[l][i]
    for l2 in range(d):
        if l2 != l and P[l2][i] == j and V[l2][i] == g:
            return False
    return True


def _adjacency(t, N, d, T, P, V, Vi, rev):
    """Adjacency lists of the lift; A-vertices are 0..tN-1 and B-vertices tN..2tN-1."""
    base = t * N
    adj = [None] * (2 * base)
    for i in range(t):
        Vrow = [V[l][i] for l in range(d)]
        Prow = [P[l][i] for l in range(d)]
        for x in range(N):
            Tx = T[x]
            adj[i * N + x] = [base + Prow[l] * N + Tx[Vrow[l]] for l in range(d)]
    for j in range(t):
        lst = rev[j]
        for y in range(N):
            Ty = T[y]
            adj[base + j * N + y] = [i * N + Ty[Vi[l][i]] for (l, i) in lst]
    return adj


def _cost(t, N, d, D, adj):
    """Total number of (fiber representative, vertex) pairs at distance > D."""
    tot = 2 * t * N
    sources = [i * N for i in range(t)] + [t * N + j * N for j in range(t)]
    total = 0
    for s in sources:
        seen = bytearray(tot)
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += tot - count
    return total


def _lift_edges(t, N, d, T, P, V):
    """Edge list of the lift; all edges are distinct and the lift is d-regular."""
    base = t * N
    edges = []
    for l in range(d):
        for i in range(t):
            j = P[l][i]
            g = V[l][i]
            for x in range(N):
                edges.append((i * N + x, base + j * N + T[x][g]))
    return edges


def _search(t, N, d, D, m, k, r, rng, deadline):
    """Anneal voltages on one group and one base graph; return lift edges with diameter <= D, or None."""
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    Inv = [inv(g) for g in range(N)]

    P = [list(range(t))] + [rng.sample(range(t), t) for _ in range(d - 1)]
    rev = [[(l, i) for l in range(d) for i in range(t) if P[l][i] == j] for j in range(t)]

    V = [[None] * t for _ in range(d)]
    Vi = [[None] * t for _ in range(d)]
    for l in range(d):
        for i in range(t):
            for _ in range(10000):
                g = rng.randrange(N)
                if _ok(V, P, l, i, g, d):
                    break
            else:
                return None
            V[l][i] = g
            Vi[l][i] = Inv[g]

    adj = _adjacency(t, N, d, T, P, V, Vi, rev)
    cur = _cost(t, N, d, D, adj)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        l = rng.randrange(d)
        i = rng.randrange(t)
        g = rng.randrange(N)
        if g == V[l][i] or not _ok(V, P, l, i, g, d):
            continue
        old, old_inv = V[l][i], Vi[l][i]
        V[l][i] = g
        Vi[l][i] = Inv[g]
        adj = _adjacency(t, N, d, T, P, V, Vi, rev)
        c = _cost(t, N, d, D, adj)
        temp = max(0.3, 3.0 * (1.0 - it / ITERS))
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            V[l][i] = old
            Vi[l][i] = old_inv
    if cur != 0:
        return None
    return _lift_edges(t, N, d, T, P, V)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

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

    M = lib._moore_bound(d, D)   # total vertex count bound for the lift
    while time.monotonic() < deadline:
        t = rng.choice([1, 2, 2, 3, 3, 4])
        lo = max(d, best[0] // (2 * t) + 1)
        hi = min(M // (2 * t), lo + SPAN)
        if hi < lo:
            continue
        N = rng.randint(lo, hi)
        groups = _groups(N)
        if not groups:
            continue
        m, k, r = rng.choice(groups)
        att_deadline = min(deadline, time.monotonic() + ATTEMPT_CAP)
        edges = _search(t, N, d, D, m, k, r, rng, att_deadline)
        if edges is not None:
            consider(2 * t * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
