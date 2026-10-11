import itertools
import math
import random
import time

import lib

ITERS = 2500             # annealing steps per (group, count matrix) try
GROUPS_PER_ATTEMPT = 40  # groups tried inside one attempt
TOP_CAND = 8             # candidates sampled from the smallest-order window
BUDGET0 = 3.0            # seconds per attempt, initially
BUDGET_GROWTH = 1.1
BUDGET_MAX = 10.0


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
# Groups of order M: semidirect products Z_m x| Z_k.
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


# ----------------------------------------------------------------------------
# NEW: multi-orbit bi-lifts.
#
# A base bipartite multigraph has `a` vertices on each side with c[i][j] darts
# from A_i to B_j. Every row and column of c sums to d. A dart (i, j, g) joins
# A_{i,x} to B_{j,x*g} for all x in G, so the lift has 2*a*|G| vertices. Left
# multiplication by any group element is an automorphism that preserves every
# orbit, so the diameter test needs only one BFS per orbit (2a sources). This
# generalises the single-orbit bi-Cayley search (a = 1) to a = 2, which gives a
# larger search space for the same vertex count.
# ----------------------------------------------------------------------------

def _count_spec(a, d, rng):
    """Random a x a count matrix with all row and column sums d, as (i, j, count) blocks."""
    if a == 1:
        return [(0, 0, d)]
    if a == 2 and d >= 2:
        x = rng.randint(1, d - 1)
        return [(0, 0, x), (0, 1, d - x), (1, 0, d - x), (1, 1, x)]
    return None


def _unreached(a, M, T, invs, blocks, D):
    """Total (orbit source, vertex) pairs not within distance D, for one source per orbit."""
    outA = [[] for _ in range(a)]
    inB = [[] for _ in range(a)]
    for i, j, gs in blocks:
        for g in gs:
            outA[i].append((j, g))
            inB[j].append((i, invs[g]))
    base = a * M
    N = 2 * base
    sources = [i * M for i in range(a)] + [base + j * M for j in range(a)]
    total = 0
    for src in sources:
        seen = bytearray(N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < base:
                    i, x = divmod(v, M)
                    row = T[x]
                    for j, g in outA[i]:
                        w = base + j * M + row[g]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    j, y = divmod(v - base, M)
                    row = T[y]
                    for i, hi in inB[j]:
                        w = i * M + row[hi]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _anneal(a, M, T, invs, spec, D, rng, iters, deadline):
    """Anneal the group elements of every dart to drive the unreached count to zero."""
    blocks = [[i, j, rng.sample(range(M), c)] for i, j, c in spec]
    cur = _unreached(a, M, T, invs, blocks, D)
    for it in range(iters):
        if cur == 0:
            return blocks
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        k = rng.randrange(len(blocks))
        gs = blocks[k][2]
        p = rng.randrange(len(gs))
        g = rng.randrange(M)
        if g in gs:
            continue
        old = gs[p]
        gs[p] = g
        v = _unreached(a, M, T, invs, blocks, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[p] = old
    return blocks if cur == 0 else None


def _attempt(a, M, d, D, rng, deadline):
    """Try groups of order M with a random count matrix until one lift has diameter <= D."""
    spec = _count_spec(a, d, rng)
    if spec is None:
        return None
    groups = _groups(M)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(M)] for x in range(M)]
        invs = [inv(g) for g in range(M)]
        blocks = _anneal(a, M, T, invs, spec, D, rng, ITERS, deadline)
        if blocks is not None:
            return a, M, blocks, T
    return None


def _lift_edges(a, M, T, blocks):
    """Expand a base multigraph lift into (n, edges)."""
    base = a * M
    edges = []
    for i, j, gs in blocks:
        for g in gs:
            for x in range(M):
                edges.append((i * M + x, base + j * M + T[x][g]))
    return 2 * base, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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
    # Candidate (n, a, M): n = 2*a*M total vertices, one group of order M per orbit.
    cands = []
    for a in (1, 2):
        for M in range(d, moore // (2 * a) + 1):
            n = 2 * a * M
            if best_n < n <= moore:
                cands.append((n, a, M))
    cands.sort()

    budget = BUDGET0
    fails = 0
    while time.monotonic() < deadline and cands:
        idx = rng.randrange(min(TOP_CAND, len(cands)))
        n, a, M = cands[idx]
        now = time.monotonic()
        att_deadline = min(deadline, now + budget)
        res = _attempt(a, M, d, D, rng, att_deadline)
        if res is None:
            fails += 1
            budget = min(BUDGET_MAX, BUDGET0 * (BUDGET_GROWTH ** fails))
            continue
        a, M, blocks, T = res
        n_, edges = _lift_edges(a, M, T, blocks)
        consider(n_, edges)
        cands = [c for c in cands if c[0] > best_n]

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
