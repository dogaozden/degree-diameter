import itertools
import math
import random
import time

import lib

MAX_GROUPS = 12     # groups tried per (a, N) attempt
ITERS = 3000        # annealing steps per (group, base matrix) try
ATTEMPT_BUDGET = 3.0


# ----------------------------------------------------------------------------
# Fallback families (cheap, always validated before use).
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
# Bold new family: balanced voltage lifts of a bipartite base graph with `a`
# vertices per side (2a base vertices), lifted over a non-abelian group G of
# order N (semidirect product Z_m x| Z_k). Lift has 2aN vertices.
#
# Base: a-by-a nonnegative integer matrix C with row and column sums d.
# Each base dart (i, j) carries C[i][j] distinct voltages g in G.
# Lift edges: A(i, x) -- B(j, x*g) for every dart (i, j, g) and x in G.
#
# Left multiplication by h in G is an automorphism of the lift (it preserves
# fibres), so distances from (i, e) for each base vertex suffice to certify
# diameter <= D. Search anneals voltages to zero the count of unreached pairs.
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


def _random_matrix(a, d, rng):
    """Sum of d random permutation matrices: nonnegative integer a-by-a, row and column sums d."""
    C = [[0] * a for _ in range(a)]
    for _ in range(d):
        p = list(range(a))
        rng.shuffle(p)
        for i in range(a):
            C[i][p[i]] += 1
    return C


def _cost(a, N, T, volt, D):
    """Total count of (fibre source, vertex) pairs not within distance D."""
    V = 2 * a * N
    nb = [[] for _ in range(V)]
    for i in range(a):
        for j in range(a):
            bj = (a + j) * N
            for g in volt[i][j]:
                for x in range(N):
                    u = i * N + x
                    w = bj + T[x][g]
                    nb[u].append(w)
                    nb[w].append(u)
    total = 0
    for f in range(2 * a):
        src = f * N  # identity of fibre f
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for w in nb[u]:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - cnt
    return total


def _search(a, N, d, D, rng, deadline, iters):
    """Anneal voltages over random groups of order N; return (T, C, volt) on success, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        C = _random_matrix(a, d, rng)
        volt = [[rng.sample(range(N), C[i][j]) if C[i][j] else [] for j in range(a)]
                for i in range(a)]
        pairs = [(i, j) for i in range(a) for j in range(a) if C[i][j]]
        cur = _cost(a, N, T, volt, D)
        for it in range(iters):
            if cur == 0 or time.monotonic() > deadline:
                break
            temp = max(0.2, 4.0 * (1.0 - it / iters))
            i, j = pairs[rng.randrange(len(pairs))]
            idx = rng.randrange(len(volt[i][j]))
            g = rng.randrange(N)
            if g in volt[i][j]:
                continue
            old = volt[i][j][idx]
            volt[i][j][idx] = g
            v = _cost(a, N, T, volt, D)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                volt[i][j][idx] = old
        if cur == 0:
            return T, C, volt
    return None


def _edges(a, N, T, volt):
    """Edge list and order of the lift described by (T, volt)."""
    E = []
    for i in range(a):
        for j in range(a):
            for g in volt[i][j]:
                for x in range(N):
                    E.append((i * N + x, (a + j) * N + T[x][g]))
    return 2 * a * N, E


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Record-matching case for D = 3.
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

    Vmax = lib._moore_bound(d, D)  # bound on total vertex count
    best_total = best[0]

    while time.monotonic() < deadline:
        feas = [a for a in (1, 2, 3)
                if max(best_total // (2 * a) + 1, d) <= Vmax // (2 * a)]
        if not feas:
            break
        a = rng.choice([2, 2, 2, 3, 3, 1])
        if a not in feas:
            a = rng.choice(feas)
        Nlo = max(best_total // (2 * a) + 1, d)
        Nhi = Vmax // (2 * a)
        N = rng.randint(Nlo, min(Nhi, Nlo + 12))

        att_deadline = min(deadline, time.monotonic() + ATTEMPT_BUDGET)
        res = _search(a, N, d, D, rng, att_deadline, ITERS)
        if res is not None:
            T, C, volt = res
            n, E = _edges(a, N, T, volt)
            consider(n, E)
            best_total = best[0]

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
