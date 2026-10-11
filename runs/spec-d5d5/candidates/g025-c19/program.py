import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per order N within one attempt
ITERS = 600                   # annealing steps per (group, connection set) try
T_HOT = 1.5                   # initial annealing temperature (in unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
SINGLE_FRACTION = 0.3         # share of time for the one-block (Cayley-type) search
TWO_BLOCK_BUDGET = 3.0        # initial per-attempt budget for the two-block search


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
# Group helpers.
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
# One-block bi-Cayley search (A_x -- B_{x s}, s in S, |S| = d).
# ----------------------------------------------------------------------------

def _unreached(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    if cur == 0:
        return S
    return None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a connection set with diameter <= D, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# NEW: two-block bi-Cayley search.
#
# Two orbits on each side: A^0, A^1 (A^i_x = i*N + x) and B^0, B^1
# (B^j_y = 2N + j*N + y). For each block pair (i, j) there is a connection
# set S_ij in Z_m x| Z_k, with
#       A^i_x ~ B^j_{x s}   for s in S_ij.
# Block sizes: |S_00| = |S_11| = a, |S_01| = |S_10| = d - a, so every vertex
# has degree d. Left multiplication preserves every block, so one source per
# block (4 total) determines the diameter. The graph has 4N vertices, which
# lets us beat the one-block order 2N for the same group size.
# ----------------------------------------------------------------------------

def _unreached2(N, T, invs, sets, D):
    """Unreached (source, vertex) pairs for the two-block graph, from one source per block."""
    Sij = [[sets[0], sets[1]], [sets[2], sets[3]]]
    Sinv = [[[invs[s] for s in Sij[i][j]] for j in range(2)] for i in range(2)]
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(4 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < 2 * N:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j in range(2):
                        base = 2 * N + j * N
                        for s in Sij[i][j]:
                            v = base + row[s]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                else:
                    j, y = divmod(u - 2 * N, N)
                    row = T[y]
                    for i in range(2):
                        base = i * N
                        for h in Sinv[i][j]:
                            v = base + row[h]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 4 * N - count
    return total


def _anneal2(N, T, invs, a, d, D, rng, iters, deadline):
    """Anneal the four connection sets to zero unreached pairs; return sets or None."""
    sizes = [a, d - a, d - a, a]
    sets = [rng.sample(range(N), sz) for sz in sizes]
    cur = _unreached2(N, T, invs, sets, D)
    for it in range(iters):
        if cur == 0:
            return sets
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        b = rng.randrange(4)
        t = rng.randrange(len(sets[b]))
        c = rng.randrange(N)
        if c in sets[b]:
            continue
        new = [list(s) for s in sets]
        new[b][t] = c
        v = _unreached2(N, T, invs, new, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            sets, cur = new, v
    if cur == 0:
        return sets
    return None


def _attempt2(N, d, D, rng, deadline):
    """Try groups of order N for the two-block search; return (T, sets) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for idx, (m, k, r) in enumerate(groups[:MAX_GROUPS_PER_ATTEMPT]):
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        a = 1 + idx % (d - 1)
        sets = _anneal2(N, T, invs, a, d, D, rng, ITERS, deadline)
        if sets is not None:
            return T, sets
    return None


def _edges2(N, T, sets):
    """Build (4N, edges) for the two-block graph."""
    Sij = [[sets[0], sets[1]], [sets[2], sets[3]]]
    edges = []
    for i in range(2):
        for j in range(2):
            for x in range(N):
                a = i * N + x
                row = T[x]
                for s in Sij[i][j]:
                    edges.append((a, 2 * N + j * N + row[s]))
    return 4 * N, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    single_deadline = start + SINGLE_FRACTION * time_limit
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
            return True
        return False

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2 and d >= 1:
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

    # Phase 1: one-block bi-Cayley search (2N vertices).
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + 6)
    cands = set(range(d + 1, top + 1))
    budget = 0.4
    while time.monotonic() < single_deadline and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= single_deadline:
                break
            att_deadline = min(single_deadline, now + budget)
            res = _attempt(N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 2

    # Phase 2: two-block bi-Cayley search (4N vertices), aiming above best_n.
    Nmax2 = lib._moore_bound(d, D) // 4
    skip = set()
    budget = TWO_BLOCK_BUDGET
    while time.monotonic() < deadline:
        lo = max(d + 1, best_n // 4 + 1)
        if lo > Nmax2:
            break
        window = [N for N in range(lo, min(Nmax2, lo + 3) + 1) if N not in skip]
        if not window:
            break
        success = False
        for N in window:
            if time.monotonic() >= deadline:
                break
            att_deadline = min(deadline, time.monotonic() + budget)
            res = _attempt2(N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, sets = res
            n, e = _edges2(N, T, sets)
            if consider(n, e):
                success = True
            else:
                skip.add(N)
            break
        if not success:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
