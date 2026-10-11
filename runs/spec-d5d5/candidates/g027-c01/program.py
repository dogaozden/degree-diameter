import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per order N within one attempt
ITERS = 800                   # annealing steps per bi-Cayley try
TOP_SLACK = 8                 # bi-Cayley orders searched up to Nmax//2 + TOP_SLACK
LIFT_ITERS = 500              # annealing steps per group for the 4-vertex lift search
LIFT_GROUPS = 25              # groups tried per order N in one lift attempt
LIFT_PHASE_FRAC = 0.55        # share of time_limit given to the lift search


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
# NEW CONSTRUCTION: 4-vertex base voltage lift over semidirect groups.
#
# Base graph: A_0, A_1 (left) and B_0, B_1 (right). The number of darts
# between each pair of base vertices is the matrix [[p, d-p], [d-p, p]], so
# every base vertex has degree d. Each dart carries a voltage g in G, and the
# lift (lib.group_lift) has 4N vertices, bipartite by construction.
#
# Left multiplication by G is an automorphism of the lift, so the diameter
# can be checked by BFS from the four base vertices at the identity.
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


def _lift_pairs(d, p):
    """Base dart endpoints (i, j): p darts A0-B0, d-p darts A0-B1, d-p darts A1-B0, p darts A1-B1."""
    return [(0, 0)] * p + [(0, 1)] * (d - p) + [(1, 0)] * (d - p) + [(1, 1)] * p


def _lift_cost(N, T, invs, pairs, volts, D):
    """Count (source, vertex) pairs not within distance D, sources = the 4 base vertices at identity."""
    Ad = [[], []]
    Bd = [[], []]
    for (i, j), g in zip(pairs, volts):
        Ad[i].append((j, g))
        Bd[j].append((i, invs[g]))
    N2 = 2 * N
    total = 0
    for src in (0, N, N2, N2 + N):
        seen = bytearray(4 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N2:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in Ad[i]:
                        w = N2 + j * N + row[g]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    j, y = divmod(u - N2, N)
                    row = T[y]
                    for i, gi in Bd[j]:
                        w = i * N + row[gi]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 4 * N - count
    return total


def _lift_anneal(N, T, invs, pairs, D, rng, iters, deadline):
    """Simulated annealing over the dart voltages to zero the unreached count."""
    L = len(pairs)
    volts = [rng.randrange(N) for _ in range(L)]
    cur = _lift_cost(N, T, invs, pairs, volts, D)
    for it in range(iters):
        if cur == 0:
            return volts
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        k = rng.randrange(L)
        c = rng.randrange(N)
        if c == volts[k]:
            continue
        old = volts[k]
        volts[k] = c
        v = _lift_cost(N, T, invs, pairs, volts, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            volts[k] = old
    return volts if cur == 0 else None


def _lift_attempt(N, d, D, rng, deadline):
    """Try groups of order N for a 4-vertex lift with diameter <= D. Returns (pairs, volts, mul) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:LIFT_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        p = rng.randint(1, d - 1)
        pairs = _lift_pairs(d, p)
        volts = _lift_anneal(N, T, invs, pairs, D, rng, LIFT_ITERS, deadline)
        if volts is not None:
            return pairs, volts, mul
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley search over semidirect products (kept as a second family).
#
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    lift_deadline = start + LIFT_PHASE_FRAC * time_limit
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

    # Phase 1: 4-vertex base voltage lifts. Only orders above the current best help.
    lo_N = max(d + 1, moore // 8)
    hi_N = moore // 4
    best_lift = lo_N - 1
    budget = 0.5
    while time.monotonic() < lift_deadline:
        first = max(lo_N, best_lift + 1)
        if first > hi_N:
            break
        for N in range(first, hi_N + 1):
            now = time.monotonic()
            if now >= lift_deadline:
                break
            res = _lift_attempt(N, d, D, rng, min(lift_deadline, now + budget))
            if res is None:
                continue
            pairs, volts, mul = res
            darts = [(i, 2 + j, g) for (i, j), g in zip(pairs, volts)]
            n, e = lib.group_lift(4, darts, N, mul)
            consider(n, e)
            best_lift = N
        budget *= 1.5

    # Phase 2: bi-Cayley search with the remaining time.
    Nmax = moore // 2   # bi-Cayley graph has 2N vertices
    top = min(Nmax, Nmax // 2 + TOP_SLACK)
    cands = set(range(d + 1, top + 1))
    cands = {N for N in cands if 2 * N > best_n}

    budget = 0.4
    while time.monotonic() < deadline and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
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
            budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
