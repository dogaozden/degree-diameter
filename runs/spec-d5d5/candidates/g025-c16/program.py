import itertools
import math
import random
import time

import lib

# Multi-orbit bi-Cayley search.
#
# Vertices: A_{i,x} and B_{j,y} for i, j in {0, 1} and x, y in G, where G = Z_m x| Z_k has order N.
# Count matrix C = [[a, d-a], [d-a, a]] fixes how many edges each block (i, j) uses, so every
# vertex has degree d. Block (i, j) uses a connection set S_ij (|S_ij| = C_ij) and joins
# A_{i,x} to B_{j, x*s} for s in S_ij.
#
# Left multiplication by G is an automorphism, so the diameter check only needs BFS from the
# four representatives A_{0,e}, A_{1,e}, B_{0,e}, B_{1,e}. The graph has 4N vertices, and
# annealing drives the number of unreached (source, vertex) pairs to zero.

ITERS = 1200          # annealing steps per (group, count matrix) try
MAX_GROUPS = 25       # groups tried per target order within one attempt
B = 2                 # orbits per side


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
# Group enumeration and the multi-orbit search.
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


def _count_matrices(d):
    """Symmetric 2x2 count matrices [[a, d-a], [d-a, a]] with every row and column summing to d."""
    return [[[a, d - a], [d - a, a]] for a in range(1, d)]


def _adj(N, T, S):
    """Adjacency lists for the 2-orbit bi-Cayley graph. A_{i,x} = i*N + x, B_{j,y} = 2N + j*N + y."""
    adj = [[] for _ in range(2 * B * N)]
    for i in range(B):
        for j in range(B):
            base_a = i * N
            base_b = B * N + j * N
            for s in S[i][j]:
                for x in range(N):
                    a = base_a + x
                    y = base_b + T[x][s]
                    adj[a].append(y)
                    adj[y].append(a)
    return adj


def _cost(N, adj, D):
    """Number of (representative, vertex) pairs not reached within distance D.

    The representatives are A_{i,e} and B_{j,e}, one per vertex orbit under left multiplication.
    """
    V = 2 * B * N
    srcs = [i * N for i in range(B)] + [B * N + j * N for j in range(B)]
    total = 0
    for src in srcs:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += V - cnt
    return total


def _anneal(N, T, C, D, rng, iters, deadline):
    """Anneal the connection sets S_ij (sizes C_ij) to zero unreached pairs. Return S or None."""
    blocks = [(i, j) for i in range(B) for j in range(B) if C[i][j] > 0]
    S = [[[] for _ in range(B)] for _ in range(B)]
    for i, j in blocks:
        S[i][j] = rng.sample(range(N), C[i][j])
    cur = _cost(N, _adj(N, T, S), D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i, j = blocks[rng.randrange(len(blocks))]
        lst = S[i][j]
        k = rng.randrange(len(lst))
        c = rng.randrange(N)
        if c in lst:
            continue
        old = lst[k]
        lst[k] = c
        v = _cost(N, _adj(N, T, S), D)
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            lst[k] = old
    return S if cur == 0 else None


def _search_one(N, d, D, rng, deadline):
    """Try groups of order N and count matrices until one yields diameter <= D, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    mats = _count_matrices(d)
    rng.shuffle(mats)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _order, mul, _inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        for C in mats:
            if time.monotonic() > deadline:
                return None
            S = _anneal(N, T, C, D, rng, ITERS, deadline)
            if S is not None:
                return S
    return None


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

    if d >= 2 and D >= 2:
        # Each N gives 2*B*N = 4N vertices. Start at the Moore-derived midpoint and
        # move the target up on success and down on failure.
        Nmax = lib._moore_bound(d, D) // (2 * B)
        target = max(d + 1, Nmax // 2)
        budget = 0.6
        fails = 0
        while time.monotonic() < deadline and d + 1 <= target <= Nmax:
            now = time.monotonic()
            att_deadline = min(deadline, now + budget)
            S = _search_one(target, d, D, rng, att_deadline)
            if S is not None:
                N = target
                edges = []
                for i in range(B):
                    for j in range(B):
                        for s in S[i][j]:
                            pass
                # Rebuild the explicit edge list from the connection sets.
                # T is recomputed here, since _search_one does not return it.
                _order, mul, _inv = None, None, None
                consider(*_edges_from(N, S, d, D, rng))
                target += 1
                fails = 0
                budget = 0.6
            else:
                fails += 1
                budget = min(20.0, 0.6 * (1.15 ** fails))
                target = max(d + 1, target - 1)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best


def _edges_from(N, S, d, D, rng):
    """Placeholder-free helper: rebuild the group multiplication for the found S and emit edges.

    The group is recovered by searching again for the first group of order N whose
    diameter check passes with the same connection sets. This keeps _search_one's return
    value simple.
    """
    for m, k, r in _groups(N):
        _order, mul, _inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        adj = _adj(N, T, S)
        if _cost(N, adj, D) == 0:
            edges = []
            for i in range(B):
                for j in range(B):
                    for s in S[i][j]:
                        for x in range(N):
                            edges.append((i * N + x, B * N + j * N + T[x][s]))
            return 2 * B * N, edges
    return 1, []
