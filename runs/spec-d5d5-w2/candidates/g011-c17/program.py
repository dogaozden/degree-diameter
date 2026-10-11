import itertools
import math
import random
import time

import lib

# ---------------------------------------------------------------------------
# Search parameters
# ---------------------------------------------------------------------------
LIFT_BUDGET = 2.5          # seconds per voltage-lift attempt (one order / base)
LIFT_ITERS = 3000          # hill-climb steps used to anneal the temperature
T_HOT_L = 3.0              # initial temperature (unreached-pair units)
T_COLD_L = 0.2             # final temperature
LIFT_WINDOW = 8            # orders N tried above the current lower bound

MAX_GROUPS_PER_ATTEMPT = 12
ITERS = 600
T_HOT = 1.5
T_COLD = 0.15
WINDOW_FRAC = 0.95
BUDGET_START = 0.4
BUDGET_CAP = 3.0


# ---------------------------------------------------------------------------
# Baseline families (cheap, always checked with lib.is_valid before use).
# ---------------------------------------------------------------------------

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


# ---------------------------------------------------------------------------
# NEW: voltage lifts over non-cyclic groups with a small bipartite base.
#
# Base graph: a A-vertices (0..a-1) and a B-vertices (a..2a-1), every vertex
# of base degree d (a random stub pairing). Each dart (u, v, g) joins
# (u, x) to (v, x*g) for all x in G. The lift is bipartite and d-regular.
#
# Left multiplication by G is an automorphism of the lift, so the distances
# from (b, e) for each base vertex b decide the diameter.
# ---------------------------------------------------------------------------

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


def _lift_cost(N, nb, darts, T, D):
    """Number of (source, vertex) pairs not within distance D, sources = identity fibre of each base vertex."""
    n = nb * N
    adj = [[] for _ in range(n)]
    for u, v, g in darts:
        ub = u * N
        vb = v * N
        for x in range(N):
            p = ub + x
            q = vb + T[x][g]
            adj[p].append(q)
            adj[q].append(p)
    bad = 0
    for b in range(nb):
        src = b * N
        seen = bytearray(n)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for w in frontier:
                for z in adj[w]:
                    if not seen[z]:
                        seen[z] = 1
                        nxt.append(z)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        bad += n - count
    return bad


def _lift_search(d, D, rng, deadline, best_n):
    """Random bipartite voltage lifts over Z_m x| Z_k with hill climbing on voltages and base stubs."""
    moore = lib._moore_bound(d, D)
    best = None
    bn = best_n
    while time.monotonic() < deadline:
        choices = [a for a in (2, 2, 3, 3, 4, 1)]
        rng.shuffle(choices)
        pick = None
        for a in choices:
            nb = 2 * a
            lo = bn // nb + 1
            hi = min(moore // nb, lo + LIFT_WINDOW)
            if lo <= hi:
                pick = (a, nb, lo, hi)
                break
        if pick is None:
            break
        a, nb, lo, hi = pick
        N = rng.randint(lo, hi)
        m, k, r = rng.choice(_groups(N))
        _, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]

        Astubs = [u for u in range(a) for _ in range(d)]
        Bstubs = [a + v for v in range(a) for _ in range(d)]
        rng.shuffle(Bstubs)
        darts = [[u, v, rng.randrange(N)] for u, v in zip(Astubs, Bstubs)]

        cur = _lift_cost(N, nb, darts, T, D)
        att_end = min(deadline, time.monotonic() + LIFT_BUDGET)
        it = 0
        while cur > 0 and time.monotonic() < att_end:
            temp = T_HOT_L * (T_COLD_L / T_HOT_L) ** min(1.0, it / LIFT_ITERS)
            it += 1
            i = rng.randrange(len(darts))
            if rng.random() < 0.3:
                # Swap B-endpoints of two darts: keeps all base degrees.
                j = rng.randrange(len(darts))
                if darts[i][1] == darts[j][1]:
                    continue
                darts[i][1], darts[j][1] = darts[j][1], darts[i][1]
                new = _lift_cost(N, nb, darts, T, D)
                if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                    cur = new
                else:
                    darts[i][1], darts[j][1] = darts[j][1], darts[i][1]
            else:
                old = darts[i][2]
                darts[i][2] = rng.randrange(N)
                new = _lift_cost(N, nb, darts, T, D)
                if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                    cur = new
                else:
                    darts[i][2] = old

        if cur == 0:
            edges = set()
            for u, v, g in darts:
                for x in range(N):
                    p = u * N + x
                    q = v * N + T[x][g]
                    edges.add((p, q) if p < q else (q, p))
            n = nb * N
            el = sorted(edges)
            if n > bn and lib.is_valid(n, el, d, D):
                best = (n, el)
                bn = n
    return best


# ---------------------------------------------------------------------------
# Legacy bi-Cayley search over semidirect products (fallback, kept from parent).
# ---------------------------------------------------------------------------

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


def _legacy_search(d, D, rng, deadline, best_n):
    """Bi-Cayley search near the top of the Moore window; returns (n, edges) or None."""
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + 6)
    if top < d + 1:
        return None
    best = None
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
            res = _attempt(N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            best = (2 * N, edges)
            bestN = max(bestN, N)
            success = True
            break
        if not success:
            if budget < BUDGET_CAP:
                budget = min(BUDGET_CAP, budget * 1.5)
            elif floor > d + 1:
                floor -= 1
    return best


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n is None or e is None:
            return
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Cheap baselines (always validated).
    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    total = max(1.0, 0.9 * time_limit - 1.0)
    end = start + total

    # Bold path: voltage lifts over non-cyclic groups with a 2a-vertex base.
    lift_end = start + 0.55 * total
    res = _lift_search(d, D, rng, lift_end, best_n)
    if res is not None:
        consider(*res)

    # Fallback path: bi-Cayley search for the remaining time.
    if time.monotonic() < end - 1.0:
        res = _legacy_search(d, D, rng, end, best_n)
        if res is not None:
            consider(*res)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
