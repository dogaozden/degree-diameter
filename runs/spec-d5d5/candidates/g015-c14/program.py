import itertools
import math
import random
import time

import lib

ATTEMPT_GROUPS = 12       # groups tried per (family, N) attempt
ITERS = 1500              # annealing steps per (group, block pattern) try
BASE_BUDGET = 0.6         # seconds for the first attempt at a given (family, N)
GROWTH = 1.25             # budget growth after each failed attempt
FAMILY_WEIGHTS = {1: 0.2, 2: 0.5, 3: 0.3}


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
# Groups: semidirect products Z_m x| Z_k of order N (cached per N).
# ----------------------------------------------------------------------------

_GROUP_CACHE = {}


def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    if N in _GROUP_CACHE:
        return list(_GROUP_CACHE[N])
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    _GROUP_CACHE[N] = out
    return list(out)


# ----------------------------------------------------------------------------
# NEW: multi-orbit bi-Cayley (block voltage) lifts.
#
# Take a orbits on the A side and a orbits on the B side, each orbit a copy of
# G (|G| = N). A block-size matrix M (a x a) with row and column sums d says how
# many edges join A-orbit i to B-orbit j. Each block (i, j) carries a set V_ij of
# k = M[i][j] distinct group elements:
#     A_i,x  --  B_j,(x * g)   for every g in V_ij.
# Left multiplication by h is an automorphism that maps every orbit to itself, so
# the diameter test only needs one BFS per orbit (2a sources in total), not one
# per vertex. M is random: a sum of d random permutation matrices, so every row
# and column sums to exactly d and the graph is d-regular and bipartite.
# Order is 2aN, so a=2 gives 4N vertices and a=1 is the plain bi-Cayley case.
# ----------------------------------------------------------------------------

def _random_pattern(a, d, rng):
    """Block-size matrix M (a x a) = sum of d random permutation matrices (row/col sums = d)."""
    M = [[0] * a for _ in range(a)]
    for _ in range(d):
        perm = list(range(a))
        rng.shuffle(perm)
        for i in range(a):
            M[i][perm[i]] += 1
    return M


def _cost(state, blocks, N, a, T, invs, D):
    """Total unreached (source, vertex) pairs, with one source per orbit."""
    nA = [[] for _ in range(a)]   # A_i -> (B orbit index, voltage g)
    nB = [[] for _ in range(a)]   # B_j -> (A orbit index, inverse voltage)
    for (i, j, _k), V in zip(blocks, state):
        for g in V:
            nA[i].append((a + j, g))
            nB[j].append((i, invs[g]))
    V_tot = 2 * a * N
    total = 0
    for o in range(2 * a):
        s = o * N
        seen = bytearray(V_tot)
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                oo, x = divmod(u, N)
                row = T[x]
                if oo < a:
                    for ob, g in nA[oo]:
                        v = ob * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    for oa, gi in nB[oo - a]:
                        v = oa * N + row[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V_tot - count
    return total


def _anneal(blocks, N, a, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over block voltage sets to zero the unreached pairs."""
    state = [rng.sample(range(N), k) for (_i, _j, k) in blocks]
    cur = _cost(state, blocks, N, a, T, invs, D)
    for it in range(iters):
        if cur == 0:
            return state
        if time.monotonic() > deadline:
            break
        temp = max(0.2, 3.0 * (1.0 - it / iters))
        bi = rng.randrange(len(blocks))
        k = blocks[bi][2]
        pos = rng.randrange(k)
        c = rng.randrange(N)
        if c in state[bi]:
            continue
        old = state[bi][pos]
        state[bi][pos] = c
        v = _cost(state, blocks, N, a, T, invs, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            state[bi][pos] = old
    return state if cur == 0 else None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N with random block patterns until one reaches diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:ATTEMPT_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        M = _random_pattern(a, d, rng)
        blocks = [(i, j, M[i][j]) for i in range(a) for j in range(a) if M[i][j] > 0]
        state = _anneal(blocks, N, a, T, invs, d, D, rng, ITERS, deadline)
        if state is not None:
            return blocks, state, T
    return None


def _edges(a, N, blocks, state, T):
    """Materialize the lift: returns (number of vertices, edge list)."""
    E = []
    for (i, j, _k), V in zip(blocks, state):
        for g in V:
            for x in range(N):
                E.append((i * N + x, (a + j) * N + T[x][g]))
    return 2 * a * N, E


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _search(d, D, rng, deadline, best):
    """Fill best = [n, edges] with the largest valid graph found before the deadline."""
    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return

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
        return

    moore = lib._moore_bound(d, D)
    fams = (1, 2, 3)
    cap = {a: moore // (2 * a) for a in fams}          # 2aN <= moore
    nt = {a: max(d + 1, int(0.45 * cap[a])) for a in fams}
    bud = {a: BASE_BUDGET for a in fams}

    while time.monotonic() < deadline:
        active = []
        for a in fams:
            need = max(nt[a], best[0] // (2 * a) + 1)   # must beat current best
            if need <= cap[a]:
                active.append(a)
        if not active:
            break
        a = rng.choices(active, weights=[FAMILY_WEIGHTS[x] for x in active])[0]
        N = max(nt[a], best[0] // (2 * a) + 1)
        nt[a] = N
        now = time.monotonic()
        att_deadline = min(deadline, now + bud[a])
        res = _attempt(a, N, d, D, rng, att_deadline)
        if res is None:
            bud[a] = min(bud[a] * GROWTH, 60.0)
            continue
        blocks, state, T = res
        n, e = _edges(a, N, blocks, state, T)
        consider(n, e)
        nt[a] = N + 1
        bud[a] = BASE_BUDGET


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 6.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]
    try:
        _search(d, D, rng, deadline, best)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
