import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic baselines (kept as safe candidates): PG(2,q) incidence, the
# Araujo-Pardo-Lopez graph for D = 3, and the generalized quadrangle W(q) for D = 4.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New main family: multi-orbit cyclic bi-Haar lifts with bitset BFS.
#
# Vertices: A_i,x = i*m + x (i < k, x in Z_m) and B_j,y = (k+j)*m + y.
# Layer L (0 <= L < d) and left orbit i carry one dart to right orbit P[L][i]
# with shift S[L][i]:  A_i,x ~ B_{P[L][i]}, x + S[L][i]  for all x.
# Every vertex then has degree exactly d (each layer is a perfect matching of
# orbits), and the graph is bipartite by construction.
#
# Distances are computed on whole Z_m orbits at once: each orbit's BFS level is
# an m-bit integer, and a shift is a cyclic rotation of that integer. Translation
# symmetry means the reps A_i,0 and B_j,0 (2k sources) determine diameter.
# ----------------------------------------------------------------------------

_BIG = 10 ** 6


def _rot(X, s, m, full):
    """Cyclically shift the m-bit set X by s (element x goes to x + s mod m)."""
    if s == 0:
        return X
    return ((X << s) | (X >> (m - s))) & full


def _cost(k, m, d, P, S, D, limit):
    """Number of (source, vertex) pairs not reached within D. Zero means diameter <= D.

    Returns early with a value above `limit` once the running total passes it.
    Duplicate edges (same left orbit, right orbit and shift) get a large penalty.
    """
    darts = [(i, P[L][i], S[L][i]) for L in range(d) for i in range(k)]
    seen = set()
    dups = 0
    for key in ((i, j, s) for i, j, s in darts):
        if key in seen:
            dups += 1
        seen.add(key)
    if dups:
        return _BIG + dups

    full = (1 << m) - 1
    N = 2 * k * m
    total = 0
    sources = [(0, i) for i in range(k)] + [(1, j) for j in range(k)]
    for side, src in sources:
        fA = [0] * k
        fB = [0] * k
        vA = [0] * k
        vB = [0] * k
        if side == 0:
            fA[src] = vA[src] = 1
        else:
            fB[src] = vB[src] = 1
        for _ in range(D):
            nA = [0] * k
            nB = [0] * k
            for i, j, s in darts:
                x = fA[i]
                if x:
                    nB[j] |= _rot(x, s, m, full)
                y = fB[j]
                if y:
                    nA[i] |= _rot(y, (m - s) % m, m, full)
            for t in range(k):
                nA[t] &= ~vA[t]
                vA[t] |= nA[t]
                nB[t] &= ~vB[t]
                vB[t] |= nB[t]
            fA, fB = nA, nB
            if not any(fA) and not any(fB):
                break
        reached = sum(v.bit_count() for v in vA) + sum(v.bit_count() for v in vB)
        total += N - reached
        if total > limit:
            return total
    return total


def _edges(k, m, d, P, S):
    """Full edge list of the lift, vertices 0..2km-1."""
    E = set()
    for L in range(d):
        for i in range(k):
            j = P[L][i]
            s = S[L][i]
            for x in range(m):
                E.add((i * m + x, (k + j) * m + (x + s) % m))
    return 2 * k * m, sorted(E)


def _random_state(d, k, m, rng):
    P = []
    S = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        P.append(perm)
        S.append([rng.randrange(m) for _ in range(k)])
    return P, S


def _anneal(d, D, k, m, rng, deadline, iters, P=None, S=None, T0=1.0):
    """Simulated annealing over shifts and orbit-matching swaps.

    Metropolis acceptance is drawn up front: a move with new cost c2 is accepted
    iff c2 <= cost - T*ln(u), u ~ Uniform(0, 1].
    Returns (cost, P, S).
    """
    if P is None:
        P, S = _random_state(d, k, m, rng)
    else:
        P = [list(r) for r in P]
        S = [list(r) for r in S]
    cost = _cost(k, m, d, P, S, D, float("inf"))
    T = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.995)
        limit = cost - T * math.log(1.0 - rng.random())
        L = rng.randrange(d)
        if k == 1 or rng.random() < 0.6:
            i = rng.randrange(k)
            old = S[L][i]
            new = rng.randrange(m)
            if new == old:
                continue
            S[L][i] = new
            c2 = _cost(k, m, d, P, S, D, limit)
            if c2 <= limit:
                cost = c2
            else:
                S[L][i] = old
        else:
            i1, i2 = rng.sample(range(k), 2)
            P[L][i1], P[L][i2] = P[L][i2], P[L][i1]
            c2 = _cost(k, m, d, P, S, D, limit)
            if c2 <= limit:
                cost = c2
            else:
                P[L][i1], P[L][i2] = P[L][i2], P[L][i1]
    return cost, P, S


def _perturb(P, S, m, rng, flips):
    """Copy of a state with a few shifts re-rolled."""
    P2 = [list(r) for r in P]
    S2 = [list(r) for r in S]
    d = len(S2)
    k = len(S2[0])
    for _ in range(flips):
        S2[rng.randrange(d)][rng.randrange(k)] = rng.randrange(m)
    return P2, S2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Algebraic candidates.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: multi-orbit cyclic bi-Haar lifts, annealed, with elite restarts.
    ks = [1, 1, 2, 2, 3, 4]
    elite = {}  # (k, m) -> (cost, P, S) of the best failed state for that size
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        lo = max(base + 1, d, 2)
        hi = lo + max(4, lo // 10)
        m = rng.randint(lo, hi)
        key = (k, m)

        P0, S0, T0 = None, None, 1.0
        if key in elite and rng.random() < 0.5:
            _, Pe, Se = elite[key]
            P0, S0 = _perturb(Pe, Se, m, rng, rng.randint(1, 3))
            T0 = 0.5

        iters = 4000 if k == 1 else 2000
        cost, P, S = _anneal(d, D, k, m, rng, deadline, iters, P0, S0, T0)
        if cost == 0:
            n, e = _edges(k, m, d, P, S)
            consider(n, e)
            continue
        if key not in elite or cost < elite[key][0]:
            elite[key] = (cost, P, S)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
