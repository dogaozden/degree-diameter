import itertools
import math
import random
import time

import lib

ITERS = 500                   # annealing steps per (group, count-matrix) try
T_HOT = 1.5                   # initial annealing temperature (in unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
MAX_GROUPS = 10               # groups tried per (base shape, order) attempt


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
# Voltage lifts over semidirect products Z_m x| Z_k with a general base shape.
#
# The base multigraph has a "A" vertices and b "B" vertices, and a count matrix
# c[u][v] of parallel darts (u -> v), with every row sum and column sum equal
# to d. Each dart carries a distinct voltage g in G = Z_m x| Z_k. The lift has
# (a+b)*N vertices, with A_u,x = u*N + x and B_v,y = a*N + v*N + y, and dart
# (u,v,g) gives edges A_u,x -- B_v,x*g.
#
# Left multiplication by G is an automorphism, so the eccentricity of one
# identity vertex per base part decides the diameter. Right-multiplying all
# voltages into B_v by a constant h is an isomorphism, so the first voltage
# of each A_0 row can be normalized to the identity.
#
# Shapes used:
#   (a, b) = (1, 1), c = [[d]]                 bi-Cayley graph, order 2N
#   (a, b) = (2, 2), c = [[p, d-p], [d-p, p]]  order 4N
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


def _unreached(N, T, invs, a, b, V, D):
    """Count (source, vertex) pairs not within distance D, with one source per base part."""
    tot = (a + b) * N
    Bofs = a * N
    Vi = [[[invs[g] for g in V[u][v]] for v in range(b)] for u in range(a)]
    total = 0
    for s in range(a + b):
        src = s * N
        seen = bytearray(tot)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for w in frontier:
                if w < Bofs:
                    u, x = divmod(w, N)
                    row = T[x]
                    for v in range(b):
                        base = Bofs + v * N
                        for g in V[u][v]:
                            z = base + row[g]
                            if not seen[z]:
                                seen[z] = 1
                                nxt.append(z)
                else:
                    v, y = divmod(w - Bofs, N)
                    row = T[y]
                    for u in range(a):
                        base = u * N
                        for h in Vi[u][v]:
                            z = base + row[h]
                            if not seen[z]:
                                seen[z] = 1
                                nxt.append(z)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += tot - count
    return total


def _anneal(N, T, invs, a, b, c, D, rng, iters, deadline):
    """Simulated annealing over the voltage lists to zero unreached pairs."""
    V = [[None] * b for _ in range(a)]
    for u in range(a):
        for v in range(b):
            k = c[u][v]
            if u == 0:
                V[u][v] = [0] + rng.sample(range(1, N), k - 1)
            else:
                V[u][v] = rng.sample(range(N), k)
    cur = _unreached(N, T, invs, a, b, V, D)
    for it in range(iters):
        if cur == 0:
            return V
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        u = rng.randrange(a)
        v = rng.randrange(b)
        lst = V[u][v]
        lo = 1 if u == 0 else 0
        if lo >= len(lst):
            continue
        i = rng.randrange(lo, len(lst))
        g = rng.randrange(N)
        if g in lst:
            continue
        old = lst[i]
        lst[i] = g
        new = _unreached(N, T, invs, a, b, V, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
        else:
            lst[i] = old
    return V if cur == 0 else None


def _attempt(a, b, N, d, D, rng, deadline):
    """Try groups of order N for base shape (a, b) until one lift has diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        if a == 1 and b == 1:
            c = [[d]]
        else:
            p = rng.randint(1, d - 1)
            c = [[p, d - p], [d - p, p]]
        V = _anneal(N, T, invs, a, b, c, D, rng, ITERS, deadline)
        if V is not None:
            return T, V
    return None


def _lift_edges(N, a, b, T, V):
    """Expand the voltage lift into (n, edges)."""
    E = []
    for u in range(a):
        for v in range(b):
            for g in V[u][v]:
                for x in range(N):
                    E.append((u * N + x, a * N + v * N + T[x][g]))
    return (a + b) * N, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 5)
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

    # Candidate (order, a, b, N). Sorted ascending so the search climbs slowly
    # from the current best order.
    cands = []
    for N in range(2, moore // 4 + 1):
        if 4 * N > best_n and 4 * N <= moore:
            cands.append((4 * N, 2, 2, N))
    for N in range(2, moore // 2 + 1):
        if 2 * N > best_n and 2 * N <= moore:
            cands.append((2 * N, 1, 1, N))
    cands.sort()

    budget = 0.5
    pending = cands
    while time.monotonic() < deadline and pending:
        nxt = []
        for idx, cand in enumerate(pending):
            if time.monotonic() >= deadline:
                nxt.extend(pending[idx:])
                break
            n_c, a, b, N = cand
            if n_c <= best_n:
                continue
            now = time.monotonic()
            att_deadline = min(deadline, now + budget)
            res = _attempt(a, b, N, d, D, rng, att_deadline)
            if res is None:
                nxt.append(cand)
                continue
            T, V = res
            n2, E = _lift_edges(N, a, b, T, V)
            consider(n2, E)
        pending = nxt
        budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
