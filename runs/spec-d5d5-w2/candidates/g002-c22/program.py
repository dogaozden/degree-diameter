import itertools
import math
import random
import time

import lib

# Voltage-lift search: a bipartite base multigraph with a x b vertices is lifted
# over a finite group G of order N (Z_m x| Z_k). Each dart (i, j) carries a voltage
# g in G and joins (A_i, x) to (B_j, x*g). Left multiplication is an automorphism,
# so the diameter is decided by BFS from one identity vertex per fiber.

ITERS = 350          # annealing steps per (group, shape, N) try
MAX_GROUPS = 12      # groups tried per attempt
T_HOT = 2.0          # initial annealing temperature (unreached-pair units)
T_COLD = 0.2         # final annealing temperature
WINDOW = 4           # how far above the current lower bound N may be sampled
BUDGET = 3.0         # seconds per attempt


# ----------------------------------------------------------------------------
# Baseline families (cheap, always checked with lib.is_valid).
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
# Group and base-graph enumeration.
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


def _shapes(d):
    """Base multigraphs as matrices c[i][j] = number of darts between A_i and B_j.

    Row sums give A-degrees and column sums give B-degrees; both are at most d.
    """
    h, l = (d + 1) // 2, d // 2
    shapes = [[[d]]]                      # 1 x 1: bi-Cayley on 2N vertices
    if d >= 2:
        shapes.append([[h, l], [l, h]])   # 2 x 2: 4N vertices
    shapes.append([[h, l]])               # 1 x 2: 3N vertices
    return shapes


def _make_darts(c):
    """Flatten the dart matrix into dart endpoints, voltage blocks, and block ids per dart."""
    darts, blocks, blk_of = [], [], []
    for i, row in enumerate(c):
        for j, mult in enumerate(row):
            if mult > 0:
                idx = []
                for _ in range(mult):
                    idx.append(len(darts))
                    darts.append((i, j))
                    blk_of.append(len(blocks))
                blocks.append(idx)
    return darts, blocks, blk_of


def _unreached(V, adj, sources, D):
    """Count (source, vertex) pairs not within distance D, summed over the given sources."""
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                for w in adj[u]:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _cost(N, a, b, darts, volt, T, D):
    """Unreached-pair count of the lift given by voltages volt."""
    V = (a + b) * N
    adj = [[] for _ in range(V)]
    for e, (i, j) in enumerate(darts):
        g = volt[e]
        base_j = (a + j) * N
        for x in range(N):
            u = i * N + x
            w = base_j + T[x][g]
            adj[u].append(w)
            adj[w].append(u)
    sources = [k * N for k in range(a + b)]
    return _unreached(V, adj, sources, D)


def _anneal(N, a, b, darts, blocks, blk_of, T, D, rng, iters, deadline):
    """Simulated annealing over voltages; voltages within one (i, j) block stay distinct."""
    volt = [0] * len(darts)
    for blk in blocks:
        for e, g in zip(blk, rng.sample(range(N), len(blk))):
            volt[e] = g
    cur = _cost(N, a, b, darts, volt, T, D)
    for it in range(iters):
        if cur == 0:
            return volt
        if time.monotonic() >= deadline:
            return None
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        e = rng.randrange(len(darts))
        blk = blocks[blk_of[e]]
        g = rng.randrange(N)
        if any(volt[f] == g for f in blk):
            continue
        old = volt[e]
        volt[e] = g
        v = _cost(N, a, b, darts, volt, T, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            volt[e] = old
    return volt if cur == 0 else None


def _attempt(N, c, d, D, rng, deadline):
    """Try groups of order N for base shape c. Return (n, edges) on success, else None."""
    a = len(c)
    b = len(c[0])
    darts, blocks, blk_of = _make_darts(c)
    if max(len(x) for x in blocks) > N:
        return None
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() >= deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        volt = _anneal(N, a, b, darts, blocks, blk_of, T, D, rng, ITERS, deadline)
        if volt is not None:
            edges = []
            for e, (i, j) in enumerate(darts):
                g = volt[e]
                for x in range(N):
                    edges.append((i * N + x, (a + j) * N + T[x][g]))
            return (a + b) * N, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
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

    # Cheap baselines (always safe; consider() validates them).
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

    shapes = _shapes(d)
    moore = lib._moore_bound(d, D)

    # Random sampling of (shape, N) with N ascending past the best found so far.
    while time.monotonic() < deadline:
        cands = []
        for c in shapes:
            v = len(c) + len(c[0])
            lo = max(2 * d, -(-(best_n + 1) // v))
            hi = min(moore // v, lo + WINDOW)
            for N in range(lo, hi + 1):
                cands.append((N, c))
        if not cands:
            break
        N, c = rng.choice(cands)
        res = _attempt(N, c, d, D, rng, min(deadline, time.monotonic() + BUDGET))
        if res is None:
            continue
        n, edges = res
        consider(n, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
