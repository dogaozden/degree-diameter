import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per order N within one attempt (2-orbit family)
ITERS = 600                   # annealing steps per (group, connection set) try (2-orbit family)
T_HOT = 1.5                   # initial annealing temperature (in unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
WINDOW_FRAC = 0.95            # search only N in [WINDOW_FRAC * top, top] first
BUDGET_START = 0.4            # seconds per (N) attempt in the first pass
BUDGET_CAP = 3.0              # cap on per-attempt seconds as passes fail

# 4-orbit family (new): base graph with two A-orbits and two B-orbits.
GROUPS_PER_N4 = 10            # groups tried per order N in the 4-orbit family
ITERS4 = 500                  # annealing steps per (group, sets) try
BUDGET4_START = 1.0           # seconds per N attempt in the 4-orbit family
BUDGET4_CAP = 6.0


# ----------------------------------------------------------------------------
# Best-so-far holder: only validated graphs are ever stored.
# ----------------------------------------------------------------------------

class _Best:
    def __init__(self, d, D):
        self.d, self.D = d, D
        self.n, self.e = 1, []

    def offer(self, n, e):
        if n > self.n and lib.is_valid(n, e, self.d, self.D):
            self.n, self.e = n, e


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
# Groups: semidirect products Z_m x|_r Z_k of order N.
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
# 2-orbit bi-Cayley search (parent family, unchanged in behaviour).
# Vertices A_x and B_y (x, y in G). Edge A_x -- B_{x s} for s in S, |S| = d.
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


def _search2(d, D, rng, deadline, best):
    """Parent's 2-orbit bi-Cayley search over orders N, with a window that widens on failure."""
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + 6)
    if top < d + 1:
        return
    floor = max(d + 1, int(WINDOW_FRAC * top))
    bestN = best.n // 2
    budget = BUDGET_START

    while time.monotonic() < deadline:
        lo = max(floor, bestN + 1)
        if lo > top:
            break
        cands = list(range(lo, top + 1))
        rng.shuffle(cands)
        success = False
        for N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            res = _attempt(N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            best.offer(2 * N, edges)
            bestN = max(bestN, N)
            success = True
            break
        if not success:
            if budget < BUDGET_CAP:
                budget = min(BUDGET_CAP, budget * 1.5)
            elif floor > d + 1:
                floor -= 1


# ----------------------------------------------------------------------------
# NEW: 4-orbit bi-Cayley family.
#
# Vertices A_{i,x}, B_{j,y} with i, j in {0, 1} and x, y in G (|G| = N), 4N total.
# Edges A_{i,x} -- B_{j, x*g} for g in S[i][j]. Left multiplication by G is an
# automorphism, so the diameter is decided by BFS from the four base vertices
# A_{0,e}, A_{1,e}, B_{0,e}, B_{1,e}.
#
# Degree is d everywhere when |S[0][0]| = |S[1][1]| = a and |S[0][1]| = |S[1][0]| = d - a.
# Compared with the 2-orbit family this gives a much larger search space per order
# (two independent connection pattern blocks), so it can reach orders the single
# orbit family cannot.
# ----------------------------------------------------------------------------

def _unreached4(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, over the four base vertices."""
    Sinv = [[[invs[g] for g in S[i][j]] for j in range(2)] for i in range(2)]
    M = 4 * N
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(M)
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
                        base = (2 + j) * N
                        for g in S[i][j]:
                            v = base + row[g]
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
        total += M - count
    return total


def _anneal4(N, T, invs, d, D, a, rng, iters, deadline):
    """Anneal the four connection sets to zero unreached pairs."""
    sizes = [[a, d - a], [d - a, a]]
    S = [[rng.sample(range(N), sizes[i][j]) for j in range(2)] for i in range(2)]
    cur = _unreached4(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(2)
        j = rng.randrange(2)
        pos = rng.randrange(sizes[i][j])
        c = rng.randrange(N)
        if c in S[i][j]:
            continue
        S2 = [[list(S[p][q]) for q in range(2)] for p in range(2)]
        S2[i][j][pos] = c
        v = _unreached4(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    if cur == 0:
        return S
    return None


def _attempt4(N, d, D, a, rng, deadline):
    """Try groups of order N for the 4-orbit family until a valid set of connection sets is found."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_N4]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal4(N, T, invs, d, D, a, rng, ITERS4, deadline)
        if S is not None:
            return T, S
    return None


def _edges4(N, T, S):
    """Edge list of the 4-orbit bi-Cayley graph (4N vertices)."""
    edges = []
    for i in range(2):
        for j in range(2):
            for x in range(N):
                row = T[x]
                for g in S[i][j]:
                    edges.append((i * N + x, (2 + j) * N + row[g]))
    return 4 * N, edges


def _search4(d, D, rng, deadline, best):
    """Search the 4-orbit family over orders N, widening the window on failure."""
    top = lib._moore_bound(d, D) // 4
    if top < d + 1:
        return
    floor = max(d + 1, int(WINDOW_FRAC * top))
    bestN = best.n // 4
    budget = BUDGET4_START

    while time.monotonic() < deadline:
        lo = max(floor, bestN + 1)
        if lo > top:
            break
        cands = list(range(lo, top + 1))
        rng.shuffle(cands)
        success = False
        for N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            a = rng.randrange(1, d)   # |S00| = |S11| = a, |S01| = |S10| = d - a
            att_deadline = min(deadline, now + budget)
            res = _attempt4(N, d, D, a, rng, att_deadline)
            if res is None:
                continue
            T, S = res
            n, edges = _edges4(N, T, S)
            best.offer(n, edges)
            bestN = max(bestN, N)
            success = True
            break
        if not success:
            if budget < BUDGET4_CAP:
                budget = min(BUDGET4_CAP, budget * 1.5)
            elif floor > d + 1:
                floor -= 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    avail = 0.85 * time_limit - 1.0
    deadline = start + avail
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = _Best(d, D)

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        best.offer(n, e)
        return best.n, best.e

    if D >= 2:
        best.offer(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            best.offer(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            best.offer(gq[0], gq[1])

    if d >= 2 and D >= 2:
        # Split the search time: the 2-orbit family gets a shorter slice first,
        # then the 4-orbit family gets the rest.
        deadline2 = start + 0.35 * avail
        _search2(d, D, rng, deadline2, best)
        _search4(d, D, rng, deadline, best)

    if not lib.is_valid(best.n, best.e, d, D):
        return 1, []
    return best.n, best.e
