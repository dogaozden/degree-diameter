import itertools
import math
import random
import time

import lib

# Multi-orbit bi-Cayley search: a base graph with `a` A-orbits and `a` B-orbits,
# lifted over a finite group G of order N (2*a*N vertices). Dart (i, j, g) joins
# A_{i,x} to B_{j,x*g} for all x in G. Left multiplication is an automorphism, so
# eccentricities only need to be read from one representative per orbit (2*a BFS runs).

ITERS = 700                 # annealing steps per (group, dart labelling) try
T_HOT = 1.5                 # initial temperature (in unreached-pair units)
T_COLD = 0.15               # final temperature
GROUPS_PER_ATTEMPT = 10     # groups tried for one order N within an attempt
ORBITS = (2, 1, 3, 2)       # orbit counts per side, rotated through
BUDGET_START = 2.5          # seconds per attempt at first
BUDGET_CAP = 8.0            # cap on per-attempt seconds as attempts keep failing
WINDOW_START = 0.97         # first search N in [WINDOW_START * top, top]
WINDOW_MIN = 0.55           # the window widens down to this fraction


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
# Multi-orbit bi-Cayley search.
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


def _pattern(a, d):
    """Base multigraph with a A-orbits and a B-orbits: A_i has darts to B_{(i+k) % a}, k < d.

    Every A_i and every B_j then has exactly d darts, so the lift has max degree d.
    """
    return [(i, (i + k) % a) for i in range(a) for k in range(d)]


def _unreached(a, N, T, invs, darts, D, sources):
    """Total count of (source, vertex) pairs not within distance D, over one source per orbit."""
    V = 2 * a * N
    base_b = a * N
    fwd = [[] for _ in range(a)]   # fwd[i]: (offset of B_j, g) for darts leaving A_i
    bwd = [[] for _ in range(a)]   # bwd[j]: (offset of A_i, g^-1) for darts entering B_j
    for i, j, g in darts:
        fwd[i].append((base_b + j * N, g))
        bwd[j].append((i * N, invs[g]))
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        reached = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < base_b:
                    i, x = divmod(u, N)
                    row = T[x]
                    for off, g in fwd[i]:
                        v = off + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - base_b, N)
                    row = T[y]
                    for off, hinv in bwd[j]:
                        v = off + row[hinv]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            reached += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - reached
    return total


def _anneal(a, N, T, invs, base, d, D, rng, iters, deadline):
    """Anneal the group label of each base dart to drive the unreached count to zero."""
    P = len(base)
    sources = [i * N for i in range(a)] + [a * N + j * N for j in range(a)]
    gs = [rng.randrange(N) for _ in range(P)]

    def darts_of(labels):
        return [(i, j, labels[t]) for t, (i, j) in enumerate(base)]

    cur = _unreached(a, N, T, invs, darts_of(gs), D, sources)
    for it in range(iters):
        if cur == 0:
            return darts_of(gs)
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        t = rng.randrange(P)
        c = rng.randrange(N)
        if c == gs[t]:
            continue
        old = gs[t]
        gs[t] = c
        v = _unreached(a, N, T, invs, darts_of(gs), D, sources)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[t] = old
    if cur == 0:
        return darts_of(gs)
    return None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N for the a-orbit base; return (T, darts) on success, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    base = _pattern(a, d)
    for m, k, r in groups[:GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        darts = _anneal(a, N, T, invs, base, d, D, rng, ITERS, deadline)
        if darts is not None:
            return T, darts
    return None


def _lift_edges(a, N, T, darts):
    """Expand darts into the explicit edge list (A vertices 0..aN-1, B vertices aN..2aN-1)."""
    out = set()
    for i, j, g in darts:
        for x in range(N):
            out.add((i * N + x, a * N + j * N + T[x][g]))
    return list(out)


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

    M = lib._moore_bound(d, D)          # total vertex bound 2*a*N <= M
    frac = {a: WINDOW_START for a in ORBITS}
    budget = BUDGET_START
    step = 0

    while time.monotonic() < deadline:
        a = ORBITS[step % len(ORBITS)]
        step += 1
        top = M // (2 * a)              # largest N allowed by the Moore bound
        if top < d or 2 * a * top <= best_n:
            continue
        lo = min(top, max(d, int(frac[a] * top)))
        N = rng.randint(lo, top)
        att_deadline = min(deadline, time.monotonic() + budget)
        res = _attempt(a, N, d, D, rng, att_deadline)
        if res is None:
            frac[a] = max(WINDOW_MIN, frac[a] - 0.02)
            budget = min(BUDGET_CAP, budget * 1.1)
            continue
        T, darts = res
        consider(2 * a * N, _lift_edges(a, N, T, darts))

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
