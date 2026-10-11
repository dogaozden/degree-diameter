import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # single-orbit: groups tried per order N
ITERS = 400                   # single-orbit: annealing steps per (group, S)
GROUPS_PER_N2 = 8             # two-orbit: groups tried per order N
ITERS2 = 3000                 # two-orbit: annealing steps per (group, t)
PHASE1_FRAC = 0.3             # fraction of time for single-orbit search


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
# Group helpers shared by both searches.
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
# Single-orbit bi-Cayley search (A_x -- B_{x s}, s in S, |S| = d).
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
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a connection set with diameter <= D."""
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
# NEW: two-orbit bi-Cayley lift (4N vertices).
#
# Vertices A_0, A_1 (orbits of size N) and B_0, B_1. The base multigraph is the
# 2x2 matrix of multiplicities c = [[t, d-t], [d-t, t]], so every base vertex
# has degree d. Each dart (i, j, g) joins A_i x to B_j (x*g) for all x in G.
# Within one (i, j) pair the voltages are distinct, so the graph is simple.
# Left multiplication is an automorphism, so the four base vertices are the only
# sources needed to test the diameter. The search space is larger than the
# single-orbit one, which lets it reach orders above 2N for the same degree.
# ----------------------------------------------------------------------------

def _two_cost(N, T, darts, D):
    """Total unreached (source, vertex) pairs for the four base sources."""
    V = 4 * N
    adj = [[] for _ in range(V)]
    for i, j, g in darts:
        ba = i * N
        bb = 2 * N + j * N
        for x in range(N):
            a = ba + x
            b = bb + T[x][g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += V - cnt
    return total


def _two_anneal(N, T, d, D, t, rng, iters, deadline):
    """Anneal voltages for the 2x2 base with multiplicity matrix [[t, d-t], [d-t, t]]."""
    counts = [(0, 0, t), (0, 1, d - t), (1, 0, d - t), (1, 1, t)]
    counts = [(i, j, c) for i, j, c in counts if c > 0]
    vol = [rng.sample(range(N), c) for _, _, c in counts]

    def flat():
        return [(i, j, g) for (i, j, _), vs in zip(counts, vol) for g in vs]

    cur = _two_cost(N, T, flat(), D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        p = rng.randrange(len(counts))
        k = rng.randrange(len(vol[p]))
        new = rng.randrange(N)
        if new in vol[p]:
            continue
        old = vol[p][k]
        vol[p][k] = new
        v = _two_cost(N, T, flat(), D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            vol[p][k] = old
    return flat() if cur == 0 else None


def _two_attempt(N, d, D, rng, deadline):
    """Try groups of order N for the two-orbit lift; return (T, darts) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_N2]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        ts = list(range(1, d // 2 + 1))   # t and d-t are equivalent by swapping B labels
        rng.shuffle(ts)
        for t in ts:
            darts = _two_anneal(N, T, d, D, t, rng, ITERS2, deadline)
            if darts is not None:
                return T, darts
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    phase1_end = start + PHASE1_FRAC * time_limit
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

    # Phase 1: single-orbit bi-Cayley search (baseline, bounded in time).
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + 3)
    cands = set(range(d + 1, top + 1))
    budget = 0.4
    while time.monotonic() < phase1_end and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= phase1_end:
                break
            att_deadline = min(phase1_end, now + budget)
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

    # Phase 2: two-orbit lift (4N vertices), searching orders above the current best.
    lo = max(d + 1, best_n // 4 + 1)
    hi = lib._moore_bound(d, D) // 4
    budget = 1.0
    while time.monotonic() < deadline and lo <= hi:
        success = False
        for N in range(lo, hi + 1):
            now = time.monotonic()
            if now >= deadline:
                break
            res = _two_attempt(N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, darts = res
            edges = [(i * N + x, 2 * N + j * N + T[x][g])
                     for (i, j, g) in darts for x in range(N)]
            consider(4 * N, edges)
            lo = N + 1
            success = True
            break
        if not success:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
