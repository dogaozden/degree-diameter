import itertools
import math
import random
import time

import lib

ITERS = 400          # annealing steps per (group, a) try
MAX_GROUPS = 40      # groups tried per order N within one attempt
WINDOW = 30          # orders N tried per sweep above the sweep start


# ----------------------------------------------------------------------------
# Baseline families (kept from the parent, used for small or special cases).
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
# NEW CONSTRUCTION: two-orbit bi-Cayley graphs ("2x2 block lifts").
#
# Take a group G of order N (semidirect products Z_m x| Z_k). Use FOUR orbits:
# A_{0,x}, A_{1,x} on one side and B_{0,y}, B_{1,y} on the other (x, y in G).
# Connection sets S_{ij} (i = A-orbit, j = B-orbit) give edges
#     A_{i,x} -- B_{j, x s}   for every s in S_{ij}.
# Vertex count is 4N, which is bipartite by construction.
#
# Block sizes: |S00| = a, |S01| = b, |S10| = b, |S11| = a with a + b = d.
# Then every A vertex has degree a + b = d and every B vertex has degree
# b + a = d.
#
# Left multiplication by G is an automorphism, so it is enough to check
# eccentricities from the four base vertices A_{0,e}, A_{1,e}, B_{0,e}, B_{1,e}.
# Single-orbit bi-Cayley graphs (the parent) are the special case of one block.
# The 2x2 block structure reaches orders near 4N, so it can hit orders that
# a single bi-Cayley search cannot.
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


def _graph2(N, T, invs, sets):
    """Adjacency lists of the 4N-vertex block graph. A_{i,x} = i*N + x, B_{j,y} = 2N + j*N + y."""
    adj = [None] * (4 * N)
    for x in range(N):
        row = T[x]
        for i in (0, 1):
            lst = []
            for j in (0, 1):
                base = 2 * N + j * N
                for s in sets[2 * i + j]:
                    lst.append(base + row[s])
            adj[i * N + x] = lst
    for y in range(N):
        row = T[y]
        for j in (0, 1):
            lst = []
            for i in (0, 1):
                for s in sets[2 * i + j]:
                    lst.append(i * N + row[invs[s]])
            adj[2 * N + j * N + y] = lst
    return adj


def _unreached2(N, adj, D):
    """Count (source, vertex) pairs at distance > D, over the four base sources."""
    V = 4 * N
    total = 0
    for src in (0, N, 2 * N, 3 * N):
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
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal2(N, T, invs, d, a, D, rng, iters, deadline):
    """Simulated annealing over the four connection sets with block sizes (a, b, b, a)."""
    b = d - a
    sizes = (a, b, b, a)
    sets = [rng.sample(range(N), sz) for sz in sizes]
    cur = _unreached2(N, _graph2(N, T, invs, sets), D)
    for it in range(iters):
        if cur == 0:
            return sets
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        k = rng.randrange(4)
        pos = rng.randrange(sizes[k])
        c = rng.randrange(N)
        if c in sets[k]:
            continue
        trial = [list(s) for s in sets]
        trial[k][pos] = c
        v = _unreached2(N, _graph2(N, T, invs, trial), D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            sets, cur = trial, v
    return sets if cur == 0 else None


def _attempt2(N, d, D, rng, deadline):
    """Try groups of order N and block splits a until one gives diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        alist = list(range(1, d))
        rng.shuffle(alist)
        for a in alist:
            if time.monotonic() > deadline:
                return None
            sets = _anneal2(N, T, invs, d, a, D, rng, ITERS, deadline)
            if sets is not None:
                return T, sets
    return None


def _edges2(N, T, sets):
    """Edge list of the 4N-vertex graph from the group table and connection sets."""
    edges = []
    for i in (0, 1):
        for j in (0, 1):
            for s in sets[2 * i + j]:
                for x in range(N):
                    edges.append((i * N + x, 2 * N + j * N + T[x][s]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

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
        return best[0], best[1]

    # Two-orbit block family: 4N vertices, N >= d, 4N <= Moore bound.
    moore = lib._moore_bound(d, D)
    max_N = moore // 4
    lo = max(d + 1, max_N // 2)
    N = lo
    bestN = 0
    budget = 0.6
    hi = min(max_N, lo + WINDOW)

    while time.monotonic() < deadline:
        if N > hi:
            # Start a new sweep above what has already succeeded, with more time per order.
            N = max(lo, bestN + 1)
            if N > max_N:
                break
            hi = min(max_N, N + WINDOW)
            budget *= 1.5
        now = time.monotonic()
        att_deadline = min(deadline, now + budget)
        res = _attempt2(N, d, D, rng, att_deadline)
        if res is not None:
            T, sets = res
            consider(4 * N, _edges2(N, T, sets))
            bestN = max(bestN, N)
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
