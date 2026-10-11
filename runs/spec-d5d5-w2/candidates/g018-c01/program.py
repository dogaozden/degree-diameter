import itertools
import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# Tunables
# ----------------------------------------------------------------------------
ITERS1 = 600          # annealing steps, single-orbit bi-Cayley search
T_HOT1 = 1.5
T_COLD1 = 0.15
WINDOW_FRAC = 0.95
BUDGET_START = 0.4
BUDGET_CAP = 3.0
ATTEMPT_GROUPS = 10

ITERS2 = 2000         # annealing steps, two-orbit search (new construction)
T_HOT2 = 3.0
T_COLD2 = 0.2
TWO_ORBIT_SHARE = 0.6  # share of the search time given to the two-orbit family
WINDOW2 = 8            # candidate orders tried above the current best order
BUDGET2_START = 0.5
BUDGET2_CAP = 4.0


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
# Groups: semidirect products Z_m x| Z_k of order N, coded as ints 0..N-1.
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
# NEW: two-orbit bi-Cayley graphs (a 4-orbit voltage lift over a group G).
#
# Vertices A^i_x and B^j_y for i, j in {0, 1} and x, y in G, so 4|G| vertices.
# Edge A^i_x -- B^j_{x s} for every s in S_ij. The four sets have sizes
#   |S_00| = a, |S_01| = d - a, |S_10| = d - a, |S_11| = a,
# so every vertex has degree exactly d. Left multiplication is an automorphism,
# so distances from the four sources A^0_0, A^1_0, B^0_0, B^1_0 decide the
# diameter. Right-multiplying all labels of B^j by h multiplies every S_ij by h,
# so identity is WLOG in S_00. Here 0 encodes the identity.
# The family has twice as many orbits as the single bi-Cayley graph, which gives
# an order of 4|G| at group orders where the single-orbit family cannot reach.
# ----------------------------------------------------------------------------

def _cost2(N, F, Gi, sets, D):
    """Number of (source, vertex) pairs not within distance D, over the four sources."""
    N2 = 2 * N
    V = 4 * N
    total = 0
    for src in (0, N, N2, N2 + N):
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N2:
                    i = 0 if u < N else 1
                    x = u - i * N
                    for j in (0, 1):
                        off = N2 + j * N
                        for s in sets[2 * i + j]:
                            v = off + F[s][x]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                else:
                    w = u - N2
                    j = 0 if w < N else 1
                    y = w - j * N
                    for i in (0, 1):
                        off = i * N
                        for s in sets[2 * i + j]:
                            v = off + Gi[s][y]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal2(N, F, Gi, d, D, a, rng, iters, deadline):
    """Anneal the four connection sets to zero unreached pairs; return sets or None."""
    sizes = (a, d - a, d - a, a)
    sets = [None] * 4
    sets[0] = [0] + rng.sample(range(1, N), a - 1)
    for k in (1, 2, 3):
        sets[k] = rng.sample(range(1, N), sizes[k])
    cur = _cost2(N, F, Gi, sets, D)
    for it in range(iters):
        if cur == 0:
            return sets
        if time.monotonic() > deadline:
            break
        temp = T_HOT2 * (T_COLD2 / T_HOT2) ** (it / iters)
        k = rng.randrange(4)
        sz = sizes[k]
        if k == 0:
            if a < 2:
                continue
            pos = rng.randrange(1, sz)   # keep identity at position 0
        else:
            pos = rng.randrange(sz)
        c = rng.randrange(1, N)
        if c in sets[k]:
            continue
        old = sets[k][pos]
        sets[k][pos] = c
        v = _cost2(N, F, Gi, sets, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            sets[k][pos] = old
    return sets if cur == 0 else None


def _attempt2(N, d, D, rng, deadline):
    """Try groups of order N for a two-orbit bi-Cayley graph with diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:ATTEMPT_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        F = [[mul(x, s) for x in range(N)] for s in range(N)]   # F[s][x] = x*s
        invs = [inv(s) for s in range(N)]
        Gi = [F[invs[s]] for s in range(N)]                      # Gi[s][y] = y*s^-1
        a = rng.randint(1, d - 1)
        sets = _anneal2(N, F, Gi, d, D, a, rng, ITERS2, deadline)
        if sets is not None:
            return N, F, sets
    return None


def _edges2(N, F, sets):
    """Edges of the two-orbit graph: A^i_x = i*N + x, B^j_y = 2N + j*N + y."""
    edges = []
    for i in (0, 1):
        for j in (0, 1):
            off_a = i * N
            off_b = 2 * N + j * N
            for s in sets[2 * i + j]:
                col = F[s]
                for x in range(N):
                    edges.append((off_a + x, off_b + col[x]))
    return edges


# ----------------------------------------------------------------------------
# Single-orbit bi-Cayley search (parent's family, kept as a fallback).
# ----------------------------------------------------------------------------

def _unreached1(N, T, invs, S, D):
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


def _anneal1(N, T, invs, d, D, rng, iters, deadline):
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached1(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT1 * (T_COLD1 / T_HOT1) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached1(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _attempt1(N, d, D, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:ATTEMPT_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal1(N, T, invs, d, D, rng, ITERS1, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

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

    # Phase 1: two-orbit bi-Cayley graphs, order 4N. Climb N from the current best.
    span = deadline - start
    two_deadline = start + TWO_ORBIT_SHARE * span
    Nmax2 = lib._moore_bound(d, D) // 4
    bestN2 = best_n // 4
    budget = BUDGET2_START
    while time.monotonic() < two_deadline:
        lo = bestN2 + 1
        if lo > Nmax2:
            break
        hi = min(Nmax2, lo + WINDOW2 - 1)
        cands = list(range(lo, hi + 1))
        rng.shuffle(cands)
        success = False
        for N in cands:
            now = time.monotonic()
            if now >= two_deadline:
                break
            res = _attempt2(N, d, D, rng, min(two_deadline, now + budget))
            if res is None:
                continue
            NN, F, sets = res
            consider(4 * NN, _edges2(NN, F, sets))
            bestN2 = max(bestN2, NN)
            success = True
            break
        if not success:
            budget = min(BUDGET2_CAP, budget * 1.5)

    # Phase 2: single-orbit bi-Cayley graphs, order 2N, for the rest of the time.
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + 6)
    if top >= d + 1:
        floor = max(d + 1, int(WINDOW_FRAC * top))
        bestN = best_n // 2
        budget = BUDGET_START
        while time.monotonic() < deadline:
            lo = max(floor, bestN + 1)
            cands = list(range(lo, top + 1))
            if not cands:
                break
            rng.shuffle(cands)
            success = False
            for N in cands:
                now = time.monotonic()
                if now >= deadline:
                    break
                att_deadline = min(deadline, now + budget)
                res = _attempt1(N, d, D, rng, att_deadline)
                if res is None:
                    continue
                T, S = res
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)
                bestN = max(bestN, N)
                success = True
                break
            if not success:
                if budget < BUDGET_CAP:
                    budget = min(BUDGET_CAP, budget * 1.5)
                elif floor > d + 1:
                    floor -= 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
