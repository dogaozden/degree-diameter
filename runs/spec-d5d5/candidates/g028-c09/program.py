import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per order N within one attempt
ITERS = 600                   # annealing steps per (group, connection sets) try
BUDGET0 = 0.5                 # initial seconds per order N


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
# Two-orbit bi-Cayley search (new in this version).
#
# Base graph: two A-orbits {A_{i,x}} and two B-orbits {B_{j,y}}, x, y in G,
# |G| = N, so 4N vertices. Edges A_{i,x} -- B_{j, x s} for s in S[i][j].
# Left multiplication by G is an automorphism, so the diameter is decided by
# BFS from the four orbit representatives A_{0,1}, A_{1,1}, B_{0,1}, B_{1,1}.
#
# Degree balance forces |S00| = |S11| = a and |S01| = |S10| = d - a, for a
# chosen per attempt. Only the four connection sets are annealed.
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


def _neighbour_lists(N, T, invs, S):
    """Adjacency lists of the two-orbit bi-Cayley graph on 4N vertices.

    A-vertices: i*N + x (i in {0,1}); B-vertices: 2N + j*N + y (j in {0,1}).
    """
    nbr = [None] * (4 * N)
    for i in (0, 1):
        for x in range(N):
            row = T[x]
            lst = []
            for j in (0, 1):
                base = 2 * N + j * N
                for s in S[i][j]:
                    lst.append(base + row[s])
            nbr[i * N + x] = lst
    for j in (0, 1):
        for y in range(N):
            row = T[y]
            lst = []
            for i in (0, 1):
                for s in S[i][j]:
                    lst.append(i * N + row[invs[s]])
            nbr[2 * N + j * N + y] = lst
    return nbr


def _unreached(N, nbr, D):
    """Total count of (source, vertex) pairs at distance > D over the four orbit sources."""
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
                for v in nbr[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal2(N, T, invs, sizes, D, rng, iters, deadline):
    """Anneal the four connection sets to zero unreached pairs; return S or None."""
    S = [[rng.sample(range(N), sizes[i][j]) if sizes[i][j] else []
          for j in (0, 1)] for i in (0, 1)]
    cur = _unreached(N, _neighbour_lists(N, T, invs, S), D)
    blocks = [(i, j) for i in (0, 1) for j in (0, 1) if sizes[i][j]]
    if not blocks:
        return None
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        i, j = rng.choice(blocks)
        k = rng.randrange(len(S[i][j]))
        c = rng.randrange(N)
        if c in S[i][j]:
            continue
        old = S[i][j][k]
        S[i][j][k] = c
        v = _unreached(N, _neighbour_lists(N, T, invs, S), D)
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            S[i][j][k] = old
    return S if cur == 0 else None


def _attempt2(N, d, D, rng, deadline):
    """Try groups of order N and balanced block sizes until a diameter-D lift appears."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        a = rng.randint(1, d - 1) if d >= 2 else 1
        sizes = [[a, d - a], [d - a, a]]
        S = _anneal2(N, T, invs, sizes, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _edges_from(N, T, S):
    """Edges of the two-orbit lift described by T and S."""
    edges = []
    for i in (0, 1):
        for j in (0, 1):
            for s in S[i][j]:
                for x in range(N):
                    edges.append((i * N + x, 2 * N + j * N + T[x][s]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    # Two-orbit lift has 4N vertices, so N <= Moore/4.
    Nmax = lib._moore_bound(d, D) // 4
    if Nmax < d + 1:
        return best

    cands = set(range(d + 1, Nmax + 1))
    budget = BUDGET0
    while time.monotonic() < deadline and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            res = _attempt2(N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, S = res
            consider(4 * N, _edges_from(N, T, S))
            # Larger orders are the only ones that can improve now.
            cands = {M for M in cands if M > N}
            success = True
            break
        if not success:
            budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
