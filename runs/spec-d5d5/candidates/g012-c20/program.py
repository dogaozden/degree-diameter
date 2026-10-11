import itertools
import math
import random
import time

import lib

GROUP_TRIES = 6        # groups tried per (a, N) configuration within one attempt
ITERS = 1500           # annealing steps per (group, base-graph) try
MAX_A = 6              # maximum number of base vertices per side
LOOKAHEAD = 40         # consider orders best+1 .. best+LOOKAHEAD
MAX_CONFIGS = 24       # cap on (order, a, N) configurations
DUP_PENALTY = 30       # cost per repeated dart (same a-end, b-end, voltage)


# ----------------------------------------------------------------------------
# Baseline families (always validated before use).
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
# Voltage lifts over a multi-vertex bipartite base.
#
# Base: a A-vertices and a B-vertices, each of base degree d, with darts
# (i, j, g): dart i -> j carrying a voltage g in a group G of order N.
# Lift: A_i fibre x in G, B_j fibre y in G, edges (A_i, x) -- (B_j, x*g).
# Order 2*a*N, bipartite, degree d. Left multiplication is an automorphism
# acting transitively on each fibre, so BFS from (A_i, e) and (B_j, e) for
# every base vertex decides the diameter.
#
# Moves: change one voltage, or swap the B-endpoints of two darts.
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


def _group_tables(m, k, r, N):
    """Multiplication table T[x][g] and inverse list for the group of order N."""
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    return T, invs


def _cost(state, a, N, T, invs, D):
    """Unreached (source, vertex) pairs at distance > D, plus penalty for repeated darts."""
    aN = a * N
    V = 2 * aN
    outA = [[] for _ in range(a)]
    inB = [[] for _ in range(a)]
    seen_t = set()
    dups = 0
    for i, j, g in state:
        outA[i].append((j, g))
        inB[j].append((i, invs[g]))
        t = (i, j, g)
        if t in seen_t:
            dups += 1
        else:
            seen_t.add(t)
    total = dups * DUP_PENALTY
    sources = [i * N for i in range(a)] + [aN + j * N for j in range(a)]
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < aN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in outA[i]:
                        v = aN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - aN, N)
                    row = T[y]
                    for i, h in inB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += V - cnt
    return total


def _anneal(a, N, T, invs, d, D, rng, iters, deadline):
    """Anneal darts and voltages; return the dart list with zero cost, or None."""
    Astub = [i for i in range(a) for _ in range(d)]
    Bstub = Astub[:]
    rng.shuffle(Bstub)
    state = [[Astub[k], Bstub[k], rng.randrange(N)] for k in range(len(Astub))]
    cur = _cost(state, a, N, T, invs, D)
    for it in range(iters):
        if cur == 0:
            return state
        if time.monotonic() > deadline:
            break
        temp = max(0.3, 3.0 * (1.0 - it / iters))
        cand = [t[:] for t in state]
        if rng.random() < 0.5 or len(cand) < 2:
            k = rng.randrange(len(cand))
            cand[k][2] = rng.randrange(N)
        else:
            k, l = rng.sample(range(len(cand)), 2)
            cand[k][1], cand[l][1] = cand[l][1], cand[k][1]
        c = _cost(cand, a, N, T, invs, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            state, cur = cand, c
    return state if cur == 0 else None


def _attempt(a, N, d, D, rng, deadline):
    """Try several groups of order N with base size a; return (T, state) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUP_TRIES]:
        if time.monotonic() >= deadline:
            return None
        T, invs = _group_tables(m, k, r, N)
        st = _anneal(a, N, T, invs, d, D, rng, ITERS, deadline)
        if st is not None:
            return T, st
    return None


def _edges(a, N, T, st):
    """Expand a successful base into (order, edges) of the lift."""
    aN = a * N
    es = set()
    for i, j, g in st:
        for x in range(N):
            es.add((i * N + x, aN + j * N + T[x][g]))
    return 2 * aN, list(es)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.82 * time_limit - 1.0)
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

    if D == 1:
        consider(2, [(0, 1)])
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

    # Candidate (order, a, N) configurations with order just above the current best.
    Mb = lib._moore_bound(d, D)
    base_best = best[0]
    configs = []
    for M in range(base_best + 1, min(Mb, base_best + LOOKAHEAD) + 1):
        for a in range(1, MAX_A + 1):
            if M % (2 * a):
                continue
            N = M // (2 * a)
            if N < 2:
                continue
            configs.append((M, a, N))
            if len(configs) >= MAX_CONFIGS:
                break
        if len(configs) >= MAX_CONFIGS:
            break

    budget = 0.8
    while time.monotonic() < deadline:
        configs = [c for c in configs if c[0] > best[0]]
        if not configs:
            break
        found_any = False
        for M, a, N in configs:
            if M <= best[0]:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(a, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, st = res
            n, e = _edges(a, N, T, st)
            consider(n, e)
            found_any = True
        if not found_any:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
