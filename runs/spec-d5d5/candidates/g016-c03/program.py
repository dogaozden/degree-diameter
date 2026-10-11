"""Multi-orbit group-lift search for bipartite graphs of max degree d and diameter D.

New idea: instead of one A-orbit and one B-orbit (a bi-Cayley graph, 2N vertices),
use a small base bipartite multigraph with a A-vertices and b B-vertices, each
base vertex having degree d, and lift it over a semidirect product Z_m x| Z_k of
order N. A dart (i, j, s) joins A_{i,x} to B_{j,x*s} for all x. The total order is
(a+b)*N, so the 2x2 base (4N vertices) lets the search hit totals such as 340 = 4*85,
which a single orbit cannot reach with the same group sizes. Candidates are scheduled
by total vertex count, so the search always aims just above the current best.
"""
import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 10   # groups tried per (shape, N) within one attempt
ITERS = 500                   # annealing steps per (group, dart set) try
T_HOT = 1.5                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
MAX_N = 400                   # largest orbit size considered (keeps tables small)
CAND_LIMIT = 40               # candidates kept per scheduling round


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
# Multi-orbit group lifts.
#
# Base: a A-vertices and b B-vertices, multiplicity matrix M (row sums and
# column sums equal to d, so the lift is d-regular). Lifted vertices:
#   A_{i,x} = i*N + x,    B_{j,y} = a*N + j*N + y,    x, y in Z_m x| Z_k.
# Dart (i, j, s) gives edges A_{i,x} -- B_{j, x*s} for all x.
# Left multiplication is an automorphism, so the diameter is checked from one
# representative per orbit.
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


def _shapes(d):
    """Base shapes (a, b, M): the single orbit pair, and the 2x2 regular bases [[k, d-k], [d-k, k]]."""
    shapes = [(1, 1, ((d,),))]
    for k in range(1, d // 2 + 1):
        shapes.append((2, 2, ((k, d - k), (d - k, k))))
    return shapes


def _init_S(M, a, b, N, rng):
    """Random dart sets: S[i][j] is a list of M[i][j] distinct group elements."""
    return [[rng.sample(range(N), M[i][j]) if M[i][j] else [] for j in range(b)]
            for i in range(a)]


def _adjacency(N, a, b, T, invs, S):
    """Adjacency lists of the lifted graph for the dart sets S."""
    nA = a * N
    adj = [None] * ((a + b) * N)
    for i in range(a):
        base = i * N
        for x in range(N):
            row = T[x]
            lst = []
            for j in range(b):
                off = nA + j * N
                for s in S[i][j]:
                    lst.append(off + row[s])
            adj[base + x] = lst
    for j in range(b):
        base = nA + j * N
        for y in range(N):
            row = T[y]
            lst = []
            for i in range(a):
                for s in S[i][j]:
                    # A_{i,x} ~ B_{j,y} iff x*s = y, i.e. x = y*s^{-1}
                    lst.append(i * N + row[invs[s]])
            adj[base + y] = lst
    return adj


def _cost(adj, sources, D, V):
    """Total number of (source, vertex) pairs not within distance D."""
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
        total += V - count
    return total


def _anneal(N, a, b, M, T, invs, D, rng, iters, deadline):
    """Simulated annealing over the dart sets to zero the unreached pairs."""
    pairs = [(i, j) for i in range(a) for j in range(b) if M[i][j] > 0]
    S = _init_S(M, a, b, N, rng)
    V = (a + b) * N
    sources = [i * N for i in range(a)] + [a * N + j * N for j in range(b)]
    cur = _cost(_adjacency(N, a, b, T, invs, S), sources, D, V)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i, j = rng.choice(pairs)
        k = rng.randrange(M[i][j])
        c = rng.randrange(N)
        lst = S[i][j]
        if c in lst:
            continue
        old = lst[k]
        lst[k] = c
        v = _cost(_adjacency(N, a, b, T, invs, S), sources, D, V)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            lst[k] = old
    return S if cur == 0 else None


def _attempt(a, b, M, N, D, rng, deadline):
    """Try groups of order N for the given base shape until one yields diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal(N, a, b, M, T, invs, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _edges(N, a, b, T, S):
    """Edge list of the lift for dart sets S."""
    nA = a * N
    edges = []
    for i in range(a):
        for j in range(b):
            for s in S[i][j]:
                for x in range(N):
                    edges.append((i * N + x, nA + j * N + T[x][s]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget_total = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget_total
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
    shapes = _shapes(d)

    def make_cands(cur_best):
        """Candidate (total, shape index, N) triples that could beat cur_best, smallest total first."""
        out = []
        for si, (a, b, M) in enumerate(shapes):
            s = a + b
            top = min(MAX_N, moore // s)
            lo = max(d, cur_best // s + 1)
            if lo > top:
                continue
            Ns = set(range(lo, min(top, lo + 4) + 1))
            x = float(lo)
            while x <= top:
                Ns.add(int(x))
                x = max(x * 1.25, x + 1)
            for N in Ns:
                if lo <= N <= top:
                    out.append((s * N, si, N))
        out.sort()
        return out[:CAND_LIMIT]

    budget = 0.4
    while time.monotonic() < deadline:
        cands = make_cands(best_n)
        if not cands:
            break
        improved = False
        for tot, si, N in cands:
            if tot <= best_n:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            a, b, M = shapes[si]
            res = _attempt(a, b, M, N, D, rng, min(deadline, now + budget))
            if res is not None:
                T, S = res
                consider(tot, _edges(N, a, b, T, S))
                improved = True
        if not improved:
            budget = min(budget * 2, 16.0)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
