import itertools
import math
import random
import time

import lib

MAX_GROUPS = 8      # groups tried per (b, N) attempt
ITERS = 1200        # annealing steps per (group, base graph) try
T_HOT = 2.0         # initial annealing temperature (unreached-pair units)
T_COLD = 0.2        # final annealing temperature
BASE_SIZES = (1, 2, 3, 4)   # base vertices per side of the voltage lift
SPAN = 4            # window of group orders tried above the current best


# ----------------------------------------------------------------------------
# Safe fallback families (always validated before use).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Generalized voltage-lift search.
#
# Base graph: b vertices A_0..A_{b-1} and b vertices B_0..B_{b-1}, with a
# d-regular bipartite multigraph of "darts" (i, j, g). Over a finite group G
# of order N, dart (i, j, g) joins A_i,x to B_j,(x*g) for every x in G.
# Left multiplication by G is an automorphism, so the diameter is decided by
# BFS from the 2b sources A_i,e and B_j,e. The graph has 2*b*N vertices.
# b = 1 recovers the bi-Cayley search; b >= 2 is the new, broader family.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _lift_nbrs(state, N, b, T, invs):
    """Neighbour lists of the lift. A_i,x is index i*N+x; B_j,y is index b*N+j*N+y."""
    off = b * N
    nbr = [[] for _ in range(2 * off)]
    for i, j, g in state:
        ig = invs[g]
        ba = i * N
        bb = off + j * N
        for x in range(N):
            y = T[x][g]
            nbr[ba + x].append(bb + y)
            nbr[bb + y].append(ba + T[y][ig])
    return nbr


def _unreached(state, N, b, T, invs, D):
    """Total count of (source, vertex) pairs at distance > D over the 2b base sources."""
    M = 2 * b * N
    nbr = _lift_nbrs(state, N, b, T, invs)
    sources = [i * N for i in range(b)] + [b * N + j * N for j in range(b)]
    total = 0
    for src in sources:
        seen = bytearray(M)
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
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += M - count
    return total


def _anneal(b, N, T, invs, d, D, rng, iters, deadline):
    """Anneal over dart states (i, j, g) to drive the unreached count to zero.

    Moves: change one dart's voltage, or swap the B-endpoints of two darts
    (this keeps every base vertex at exactly d darts, so degrees stay <= d).
    """
    n_darts = b * d
    As = [i for i in range(b) for _ in range(d)]
    Bs = As[:]
    rng.shuffle(Bs)
    state = [[As[k], Bs[k], rng.randrange(N)] for k in range(n_darts)]
    cur = _unreached(state, N, b, T, invs, D)
    for it in range(iters):
        if cur == 0:
            return state
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        new = [s[:] for s in state]
        p = rng.randrange(n_darts)
        if rng.random() < 0.5:
            new[p][2] = rng.randrange(N)
        else:
            q = rng.randrange(n_darts)
            if p == q or new[p][1] == new[q][1]:
                continue
            new[p][1], new[q][1] = new[q][1], new[p][1]
        v = _unreached(new, N, b, T, invs, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            state, cur = new, v
    if cur == 0:
        return state
    return None


def _edges(state, N, b, T):
    """Expand a dart state into the lifted (n, edges), with A-index < B-index in each pair."""
    off = b * N
    E = set()
    for i, j, g in state:
        for x in range(N):
            E.add((i * N + x, off + j * N + T[x][g]))
    return 2 * off, sorted(E)


def _attempt(b, N, d, D, rng, deadline):
    """Try groups of order N for base size b until a valid lift is found or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        state = _anneal(b, N, T, invs, d, D, rng, ITERS, deadline)
        if state is not None:
            return _edges(state, N, b, T)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    moore = lib._moore_bound(d, D)
    budget = 0.5
    while time.monotonic() < deadline:
        best_n = best[0]
        pool = []
        for b in BASE_SIZES:
            lo = max(2, best_n // (2 * b) + 1)
            hi = min(lo + SPAN, moore // (2 * b))
            for N in range(lo, hi + 1):
                pool.append((b, N))
        if not pool:
            break
        rng.shuffle(pool)
        success = False
        for b, N in pool:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(b, N, d, D, rng, min(deadline, now + budget))
            if res is not None:
                consider(*res)
                success = True
                break
        if not success:
            budget = min(budget * 1.5, 8.0)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
