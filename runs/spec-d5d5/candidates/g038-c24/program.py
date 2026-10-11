import itertools
import math
import random
import time

import lib

MAX_GROUPS = 12      # groups tried per (b, N) attempt
ITERS = 600          # annealing steps per (group, block matrix) try
FAIL_STOP = 3        # stop a scan after this many consecutive failed orders
ATTEMPT_BUDGET = 4.0 # seconds per (b, N) attempt


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
# Multi-block bi-Cayley search over semidirect products Z_m x| Z_k.
#
# The graph has b "A" blocks and b "B" blocks, each a copy of G of order N.
# A-block i, element x  -- B-block j, element x*s   for s in S[(i, j)].
# Left multiplication by G is an automorphism, so the diameter is decided by
# BFS from one identity vertex in each block (2b sources).
# The block-count matrix M[i][j] = |S[(i,j)]| has all row and column sums d.
# For b = 1 this is the single-block bi-Cayley family; for b = 2 it is a
# genuinely different base graph (two A-blocks and two B-blocks).
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


def _matrices(b, d):
    """Block-count matrices (dict (i, j) -> count) with all row and column sums d."""
    if b == 1:
        return [{(0, 0): d}]
    out = []
    for p in range(1, d // 2 + 1):
        out.append({(0, 0): p, (0, 1): d - p, (1, 0): d - p, (1, 1): p})
    return out


def _adj(b, N, T, invs, S):
    """Adjacency lists for the multi-block bi-Cayley graph with connection sets S."""
    V = 2 * b * N
    adj = [[] for _ in range(V)]
    for (i, j), elems in S.items():
        base_a = i * N
        base_b = b * N + j * N
        inv_e = [invs[s] for s in elems]
        for x in range(N):
            Tx = T[x]
            ax = adj[base_a + x]
            for s in elems:
                ax.append(base_b + Tx[s])
        for y in range(N):
            Ty = T[y]
            by = adj[base_b + y]
            for si in inv_e:
                by.append(base_a + Ty[si])
    return adj


def _cost(b, N, adj, D):
    """Total number of (source, vertex) pairs not within distance D, over all block identities."""
    V = 2 * b * N
    sources = [i * N for i in range(b)] + [b * N + j * N for j in range(b)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
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
            if count == V:
                break
        total += V - count
    return total


def _edges(b, N, T, S):
    """Edge list and vertex count of the bi-Cayley graph."""
    edges = []
    for (i, j), elems in S.items():
        for x in range(N):
            Tx = T[x]
            for s in elems:
                edges.append((i * N + x, b * N + j * N + Tx[s]))
    return 2 * b * N, edges


def _anneal(b, N, T, invs, M, D, rng, iters, deadline):
    """Simulated annealing over connection sets with block counts M to zero the unreached pairs."""
    S = {key: rng.sample(range(N), c) for key, c in M.items()}
    keys = list(M.keys())
    cur = _cost(b, N, _adj(b, N, T, invs, S), D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        key = rng.choice(keys)
        lst = S[key]
        g = rng.randrange(N)
        if g in lst:
            continue
        t = rng.randrange(len(lst))
        old = lst[t]
        lst[t] = g
        v = _cost(b, N, _adj(b, N, T, invs, S), D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            lst[t] = old
    return S if cur == 0 else None


def _attempt(b, N, d, D, rng, deadline, mats):
    """Try groups of order N and block matrices until one gives diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        order_mats = mats[:]
        rng.shuffle(order_mats)
        for M in order_mats:
            if time.monotonic() > deadline:
                return None
            S = _anneal(b, N, T, invs, M, D, rng, ITERS, deadline)
            if S is not None:
                return T, S
    return None


def _scan(b, d, D, rng, deadline, consider):
    """Ascending scan over block orders N for a b-block bi-Cayley family."""
    Nmax = lib._moore_bound(d, D) // (2 * b)
    lo = max(d + 1, int(0.4 * Nmax))
    mats = _matrices(b, d)
    if not mats or lo > Nmax:
        return
    fails = 0
    N = lo
    while N <= Nmax and fails < FAIL_STOP:
        now = time.monotonic()
        if now >= deadline:
            break
        att_deadline = min(deadline, now + ATTEMPT_BUDGET)
        res = _attempt(b, N, d, D, rng, att_deadline, mats)
        if res is None:
            fails += 1
        else:
            T, S = res
            n, e = _edges(b, N, T, S)
            consider(n, e)
            fails = 0
        N += 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.72 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0] = n
            best[1] = e

    # Record-matching calibration: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

    # Safe fallbacks.
    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Bold search: two-block bi-Cayley (new base graph) first, then single-block.
    if d >= 2 and D >= 2:
        _scan(2, d, D, rng, min(start + 0.4 * total, start + total), consider)
        _scan(1, d, D, rng, start + total, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
