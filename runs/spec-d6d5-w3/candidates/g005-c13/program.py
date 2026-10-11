import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic families: projective plane (D = 3), Araujo-Pardo-Lopez (D = 3),
# generalized quadrangle W(q) (D = 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 9 for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Single-orbit bi-Cayley graphs over small groups (different from voltage lifts).
#
# Group G of order N0 (semidirect product Z_m x| Z_k).  Vertices are
# A_g = g and B_h = G + h.  Connection set S of d distinct group elements gives
# edges A_g -- B_{g*s} for every s in S.  Left multiplication is an automorphism,
# so the distance profile only needs BFS from A_e and B_e.  Degree is exactly d,
# and the graph is bipartite by construction.
# ----------------------------------------------------------------------------

def _groups_of_order(N0):
    """All (m, k, r) with m*k = N0 that define a semidirect product Z_m x| Z_k."""
    out = []
    for k in range(1, N0 + 1):
        if N0 % k:
            continue
        m = N0 // k
        if m < 2:
            continue
        if k == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _missing(adj, N, src, D):
    """Number of vertices NOT within distance D of src."""
    seen = bytearray(N)
    seen[src] = 1
    frontier = [src]
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
    return N - count


def _anneal_bicay(d, D, N0, mul, inv, rng, deadline, budget):
    """Search a connection set S (|S| = d) so the bi-Cayley graph has diameter <= D.

    Returns S (list of group elements) or None.
    """
    if d > N0:
        return None
    rc = {}

    def right(s):
        t = rc.get(s)
        if t is None:
            t = [mul(g, s) for g in range(N0)]
            rc[s] = t
        return t

    N = 2 * N0

    def build_adj(S):
        rs = [right(s) for s in S]
        ri = [right(inv(s)) for s in S]
        adj = [None] * N
        for g in range(N0):
            adj[g] = [N0 + r[g] for r in rs]
        for h in range(N0):
            adj[N0 + h] = [r[h] for r in ri]
        return adj

    def cost(S):
        adj = build_adj(S)
        return _missing(adj, N, 0, D) + _missing(adj, N, N0, D)

    evals = 0
    while evals < budget and time.monotonic() < deadline:
        S = rng.sample(range(N0), d)
        c = cost(S)
        evals += 1
        T = 2.0
        stall = 0
        while c > 0 and stall < 400 and evals < budget:
            if time.monotonic() >= deadline:
                break
            i = rng.randrange(d)
            cand = rng.randrange(N0)
            if cand in S:
                stall += 1
                continue
            T2 = S[:]
            T2[i] = cand
            c2 = cost(T2)
            evals += 1
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / max(T, 1e-3)):
                if c2 < c:
                    stall = 0
                else:
                    stall += 1
                S, c = T2, c2
            else:
                stall += 1
            T = max(0.2, T * 0.995)
        if c == 0:
            return S
    return None


def _bicay_graph(N0, mul, S):
    """Edges of the bi-Cayley graph: A_g -- B_{mul(g, s)} for s in S."""
    edges = [(g, N0 + mul(g, s)) for g in range(N0) for s in S]
    return 2 * N0, edges


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
    ar = _araujo(d)
    if ar is not None:
        consider(ar[0], ar[1])

    if D == 3:
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Bold family: single-orbit bi-Cayley graphs over semidirect products.
    # Target orders above the current best; the search only ever replaces the
    # result when lib.is_valid confirms the new graph.
    while time.monotonic() < deadline:
        target = best_n // 2 + 1 + rng.randrange(0, 3)
        groups = _groups_of_order(target)
        if not groups:
            continue
        rng.shuffle(groups)
        found = False
        for (m, k, r) in groups[:4]:
            if time.monotonic() >= deadline:
                break
            if target < d:
                break
            order, mul, inv = lib.semidirect_group(m, k, r)
            S = _anneal_bicay(d, D, order, mul, inv, rng, deadline, 1500)
            if S is not None:
                n, e = _bicay_graph(order, mul, S)
                consider(n, e)
                found = True
                break
        if not found and time.monotonic() >= deadline:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
