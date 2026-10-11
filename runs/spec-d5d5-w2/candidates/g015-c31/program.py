import itertools
import math
import random
import time

import lib

# Generalised bi-Cayley ("lift") search.
#
# The graph has a base vertices on each side. Vertex (A, i, x) and (B, j, y),
# with x, y in a group G of order N. Each base dart t = (i, j) with voltage h
# gives the edges (A, i, x) -- (B, j, x*h) for all x. The base is a random
# sum of d permutation matrices, so every lifted vertex has degree exactly d.
# Left translation by G is an automorphism, so only one source per fibre
# needs a BFS: 2a sources in total.
#
# Simulated annealing over the voltages drives the number of unreached pairs
# to zero. The search targets orders just above the best graph found so far.

ITERS = 500
T_HOT = 1.2
T_COLD = 0.1
A_MAX = 6
BUDGET_START = 0.8
BUDGET_CAP = 6.0


# ----------------------------------------------------------------------------
# Baseline families (fast, validated before use).
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
# Group lift search over semidirect products Z_m x|_r Z_k of order N.
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


def _tables(N, m, k, r):
    """Multiplication table T[x][g] = x*g and inverses for the group (identity is index 0)."""
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    return T, invs


def _random_pairs(a, d, rng):
    """Base darts (i, j): a sum of d random permutation matrices, so every row and column has d darts."""
    pairs = []
    for _ in range(d):
        p = list(range(a))
        rng.shuffle(p)
        pairs.extend((i, p[i]) for i in range(a))
    return pairs


def _unreached(a, N, d, D, T, pairs, vol, invs):
    """Count (source, vertex) pairs not within distance D, for one source per fibre."""
    darts_A = [[] for _ in range(a)]
    darts_B = [[] for _ in range(a)]
    for (i, j), h in zip(pairs, vol):
        darts_A[i].append((j, h))
        darts_B[j].append((i, invs[h]))
    side = a * N
    tot = 2 * side
    srcs = [i * N for i in range(a)] + [side + j * N for j in range(a)]
    total = 0
    for src in srcs:
        seen = bytearray(tot)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < side:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, h in darts_A[i]:
                        v = side + j * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - side, N)
                    row = T[y]
                    for i, hi in darts_B[j]:
                        v = i * N + row[hi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += tot - count
    return total


def _anneal(a, N, d, D, T, invs, rng, deadline, iters):
    """Anneal voltages on a random base so that every pair is within distance D."""
    pairs = _random_pairs(a, d, rng)
    vol = []
    for t, (i, j) in enumerate(pairs):
        taken = {vol[s] for s in range(t) if pairs[s] == (i, j)}
        while True:
            c = rng.randrange(N)
            if c not in taken:
                break
        vol.append(c)
    cur = _unreached(a, N, d, D, T, pairs, vol, invs)
    for it in range(iters):
        if cur == 0:
            return pairs, vol
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        t = rng.randrange(len(pairs))
        c = rng.randrange(N)
        if c == vol[t]:
            continue
        if any(vol[s] == c for s in range(len(pairs)) if s != t and pairs[s] == pairs[t]):
            continue
        old = vol[t]
        vol[t] = c
        v = _unreached(a, N, d, D, T, pairs, vol, invs)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            vol[t] = old
    if cur == 0:
        return pairs, vol
    return None


def _lift_edges(a, N, T, pairs, vol):
    """Edge list of the lifted graph: vertex count 2aN, A side first."""
    side = a * N
    edges = []
    for x in range(N):
        row = T[x]
        for (i, j), h in zip(pairs, vol):
            edges.append((i * N + x, side + j * N + row[h]))
    return 2 * side, edges


def _search(a, N, d, D, rng, deadline):
    """Try groups of order N for base size a until a valid lift is found or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    idx = 0
    while time.monotonic() < deadline:
        m, k, r = groups[idx % len(groups)]
        idx += 1
        T, invs = _tables(N, m, k, r)
        res = _anneal(a, N, d, D, T, invs, rng, deadline, ITERS)
        if res is not None:
            pairs, vol = res
            return _lift_edges(a, N, T, pairs, vol)
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.3, min(0.85 * time_limit, time_limit - 2.0))
    rng = random.Random(seed)

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d < 1 or D < 1:
        return best

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and d >= 2 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    # Safe baselines.
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

    moore = lib.moore_bound(d, D)
    AS = list(range(1, A_MAX + 1))
    budget = {a: BUDGET_START for a in AS}
    fails = {a: 0 for a in AS}

    # Target: for each base size a, the smallest group order whose lift
    # strictly beats the current best graph.
    while time.monotonic() < deadline:
        cands = []
        for a in AS:
            N = max(d, best[0] // (2 * a) + 1)
            if 2 * a * N <= moore:
                cands.append(a)
        if not cands:
            break
        a = min(cands, key=lambda s: (fails[s], rng.random()))
        N = max(d, best[0] // (2 * a) + 1)
        now = time.monotonic()
        if now >= deadline:
            break
        res = _search(a, N, d, D, rng, min(deadline, now + budget[a]))
        if res is None:
            fails[a] += 1
            if fails[a] % 2 == 0:
                budget[a] = min(BUDGET_CAP, budget[a] * 1.5)
        else:
            consider(*res)
            fails[a] = 0

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
