import itertools
import math
import random
import time

import lib

ITERS = 500            # annealing steps per (group, base graph) try
MAX_GROUPS = 10        # groups tried per (N, c) attempt


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
# NEW IDEA: multi-orbit voltage lifts with a random configuration-model base.
#
# Base graph: c "A-orbit" vertices and c "B-orbit" vertices, every base vertex of
# degree d. Its darts are a random bipartite multigraph (configuration model),
# each dart (i, j, g) carrying a voltage g in a finite group G of order N.
# Lift: vertices A_i x (x in G), B_j y (y in G), edges A_i x -- B_j (x*g).
# Left multiplication by G is an automorphism, so eccentricities of the 2c
# identity vertices decide the diameter (one BFS per base vertex).
# Annealing moves: re-voltage a dart, or swap the B-endpoints of two darts
# (which keeps every base degree equal to d). c = 1 is ordinary bi-Cayley;
# c >= 2 is the new richer search space, giving vertex count 2cN.
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


def _lift_adj(N, c, darts, T):
    """Adjacency lists of the lift. A_i x -> index i*N + x; B_j y -> index (c + j)*N + y."""
    V = 2 * c * N
    adj = [[] for _ in range(V)]
    for i, j, g in darts:
        bj = (c + j) * N
        ai = i * N
        for x in range(N):
            a = ai + x
            b = bj + T[x][g]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _unreached(adj, V, sources, D):
    """Count (source, vertex) pairs not within distance D, summed over the given sources."""
    total = 0
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        count = 1
        frontier = [s]
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


def _cost(N, c, darts, T, D):
    V = 2 * c * N
    adj = _lift_adj(N, c, darts, T)
    sources = [i * N for i in range(c)] + [(c + j) * N for j in range(c)]
    return _unreached(adj, V, sources, D)


def _multi_anneal(N, c, d, D, T, rng, deadline, iters):
    """Anneal a random base multigraph plus voltages to zero unreached pairs; None on failure."""
    stubs_a = [i for i in range(c) for _ in range(d)]
    stubs_b = list(stubs_a)
    rng.shuffle(stubs_b)
    darts = [(i, j, rng.randrange(N)) for i, j in zip(stubs_a, stubs_b)]
    cur = _cost(N, c, darts, T, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        new = list(darts)
        if rng.random() < 0.2 and len(new) >= 2:
            p, q2 = rng.sample(range(len(new)), 2)
            i1, j1, g1 = new[p]
            i2, j2, g2 = new[q2]
            new[p] = (i1, j2, g1)
            new[q2] = (i2, j1, g2)
        else:
            k = rng.randrange(len(new))
            i, j, _ = new[k]
            new[k] = (i, j, rng.randrange(N))
        v = _cost(N, c, new, T, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = new, v
    return darts if cur == 0 else None


def _attempt(N, c, d, D, rng, deadline):
    """Try groups of order N for a c-orbit base; return (T, darts) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        darts = _multi_anneal(N, c, d, D, T, rng, deadline, ITERS)
        if darts is not None:
            return T, darts
    return None


def _edges(N, c, darts, T):
    E = set()
    for i, j, g in darts:
        for x in range(N):
            a = i * N + x
            b = (c + j) * N + T[x][g]
            E.add((a, b))
    return sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
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

    Nmax = lib._moore_bound(d, D)
    spread = 2
    budget = 1.0

    while time.monotonic() < deadline:
        # Orders reachable with c orbits per side: 2cN must beat best_n.
        feasible = [c for c in (1, 2, 3)
                    if max(d + 1, best_n // (2 * c) + 1) <= Nmax // (2 * c)]
        if not feasible:
            break
        c = rng.choice(feasible)
        lo = max(d + 1, best_n // (2 * c) + 1)
        hi = min(Nmax // (2 * c), lo + spread)
        N = rng.randint(lo, hi)
        now = time.monotonic()
        att_deadline = min(deadline, now + budget)
        res = _attempt(N, c, d, D, rng, att_deadline)
        if res is None:
            spread += 1
            continue
        T, darts = res
        consider(2 * c * N, _edges(N, c, darts, T))
        spread = 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
