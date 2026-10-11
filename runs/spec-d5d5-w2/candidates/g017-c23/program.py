import itertools
import math
import random
import time

import lib

# Multi-base voltage lift search.
# A base multigraph with b vertices per side and d darts per vertex (a random
# d-regular bipartite multigraph, built as a sum of d permutation matrices) is
# lifted over a semidirect product Z_m x| Z_k of order N. Left multiplication
# is an automorphism of every lift, so one BFS source per base vertex suffices.
# Voltages are annealed to minimise the number of pairs farther than D apart.
# b = 1 is the bi-Cayley case from the parent; b = 2, 3 give 4N and 6N vertices.

MAX_GROUPS_PER_ATTEMPT = 8
ITERS = 900
T_HOT = 1.5
T_COLD = 0.15
WINDOW = 10
BUDGET_START = 0.8
BUDGET_CAP = 6.0
BASE_SIZES = (1, 2, 2, 3)
FRAC_START = 0.52     # target order as a fraction of the Moore bound
FRAC_MIN = 0.40


# ----------------------------------------------------------------------------
# Baseline families (fast fallbacks, validated before use).
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
# Multi-base voltage lift over semidirect products.
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


def _random_pattern(b, d, rng):
    """Darts (i, j) of a random d-regular bipartite multigraph on b + b vertices.

    Built as a sum of d random permutation matrices, so every A_i and every B_j
    has exactly d darts.
    """
    counts = [[0] * b for _ in range(b)]
    for _ in range(d):
        perm = list(range(b))
        rng.shuffle(perm)
        for i in range(b):
            counts[i][perm[i]] += 1
    pattern = []
    for i in range(b):
        for j in range(b):
            pattern += [(i, j)] * counts[i][j]
    return pattern


def _unreached(b, N, T, Tinv, pattern, gs, d, D):
    """Total (source, vertex) pairs at distance > D, one source per base vertex.

    Vertex ids: A_i, x -> i*N + x ; B_j, y -> (b + j)*N + y.
    Edge (i, j, g): A_i, x ~ B_j, x*g.  So B_j, y ~ A_i, y*g^{-1}.
    """
    V = 2 * b * N
    bN = b * N
    adjA = [[] for _ in range(b)]
    adjB = [[] for _ in range(b)]
    for (i, j), g in zip(pattern, gs):
        adjA[i].append((j, g))
        adjB[j].append((i, Tinv[g]))
    total = 0
    sources = [i * N for i in range(b)] + [(b + j) * N for j in range(b)]
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < bN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in adjA[i]:
                        v = (b + j) * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - bN, N)
                    row = T[y]
                    for i, h in adjB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - cnt
    return total


def _anneal(b, N, T, Tinv, pattern, d, D, rng, deadline):
    """Anneal the voltages of a fixed dart pattern to zero unreached pairs.

    Darts sharing the same (i, j) keep distinct voltages, so no multi-edges arise.
    """
    P = len(pattern)
    by_pair = {}
    for idx, key in enumerate(pattern):
        by_pair.setdefault(key, []).append(idx)
    gs = [0] * P
    for idxs in by_pair.values():
        vals = rng.sample(range(N), len(idxs))
        for idx, v in zip(idxs, vals):
            gs[idx] = v
    cur = _unreached(b, N, T, Tinv, pattern, gs, d, D)
    for it in range(ITERS):
        if cur == 0:
            return gs
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        k = rng.randrange(P)
        key = pattern[k]
        g = rng.randrange(N)
        if any(gs[o] == g for o in by_pair[key] if o != k):
            continue
        old = gs[k]
        if g == old:
            continue
        gs[k] = g
        v = _unreached(b, N, T, Tinv, pattern, gs, d, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[k] = old
    return gs if cur == 0 else None


def _edges(b, N, T, pattern, gs):
    """Expand the lift into (n, edges)."""
    edges = []
    for (i, j), g in zip(pattern, gs):
        for x in range(N):
            edges.append((i * N + x, (b + j) * N + T[x][g]))
    return 2 * b * N, edges


def _attempt(b, N, d, D, rng, deadline):
    """Try groups of order N with a random base multigraph on b + b vertices."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        Tinv = [inv(g) for g in range(N)]
        pattern = _random_pattern(b, d, rng)
        gs = _anneal(b, N, T, Tinv, pattern, d, D, rng, deadline)
        if gs is not None:
            return _edges(b, N, T, pattern, gs)
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.5
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
    frac = FRAC_START
    fails = 0
    while time.monotonic() < deadline:
        # Candidate base sizes b with a usable window of orders N near frac * Moore.
        opts = []
        for b in BASE_SIZES:
            lo = max(best_n // (2 * b) + 1, d + 1)
            top = min(moore // (2 * b), max(int(frac * moore) // (2 * b), lo + 2))
            if lo <= top:
                opts.append((b, lo, top))
        if not opts:
            break
        b, lo, top = rng.choice(opts)
        N = rng.randint(max(lo, top - WINDOW), top)
        now = time.monotonic()
        budget = min(BUDGET_CAP, BUDGET_START * (1.2 ** fails))
        res = _attempt(b, N, d, D, rng, min(deadline, now + budget))
        if res is None:
            fails += 1
            frac = max(FRAC_MIN, frac - 0.003)
            frac = max(frac, best_n / moore + 0.01)
        else:
            n, e = res
            consider(n, e)
            fails = 0

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
