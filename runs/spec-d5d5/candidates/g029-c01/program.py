import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per order within one attempt
ITERS = 400                   # annealing steps per bi-Cayley (group, connection set) try
LIFT_ITERS = 1500             # annealing steps per two-orbit lift (group, voltages) try


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
# Shared group helpers.
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
# Bi-Cayley search over semidirect products (one base vertex per side).
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


def _bicayley_search(d, D, rng, deadline, consider):
    """Grow bi-Cayley graphs (2N vertices) as far as the deadline allows."""
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + 3)
    cands = set(range(d + 1, top + 1))
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
            budget *= 2


# ----------------------------------------------------------------------------
# NEW: two-orbit lifts over groups (four base vertices: A_0, A_1, B_0, B_1).
#
# Each base vertex gives a block of m vertices, so n = 4m. Dart counts
# M = [[a, d-a], [d-a, a]] make every base vertex have degree d. Each dart
# (u, v) with voltage g joins (u, x) to (v, x*g). Distinct voltages on the
# same base pair keep the graph simple and the degrees exact.
#
# Left multiplication by any h is an automorphism, so a vertex (c, x) is at
# distance <= D from every other vertex iff the four sources (c, e) reach all
# vertices within D. Annealing over voltages minimises the unreached count.
# ----------------------------------------------------------------------------

def _dart_slots(d, a):
    """Base darts as (A index, B index) pairs; A_0=0, A_1=1, B_0=2, B_1=3."""
    counts = {(0, 0): a, (0, 1): d - a, (1, 0): d - a, (1, 1): a}
    slots = []
    for (u, v), c in counts.items():
        slots += [(u, 2 + v)] * c
    return slots


def _init_vol(m, slots, rng):
    """Random voltages, distinct within each base pair."""
    vol = [0] * len(slots)
    for pair in set(slots):
        idx = [i for i, s in enumerate(slots) if s == pair]
        for i, g in zip(idx, rng.sample(range(m), len(idx))):
            vol[i] = g
    return vol


def _lift_unreached(m, slots, vol, T, D):
    """Count (source, vertex) pairs at distance > D for the four base sources (c, identity)."""
    n = 4 * m
    adj = [[] for _ in range(n)]
    for (u, bidx), g in zip(slots, vol):
        ub = u * m
        bb = bidx * m
        for x in range(m):
            a = ub + x
            b = bb + T[x][g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for c in range(4):
        src = c * m
        seen = bytearray(n)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for a in frontier:
                for b in adj[a]:
                    if not seen[b]:
                        seen[b] = 1
                        nxt.append(b)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += n - count
    return total


def _lift_anneal(m, slots, T, D, rng, iters, deadline):
    """Anneal voltages to zero the unreached count; return voltages or None."""
    nd = len(slots)
    vol = _init_vol(m, slots, rng)
    cur = _lift_unreached(m, slots, vol, T, D)
    for it in range(iters):
        if cur == 0:
            return vol
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(nd)
        pair = slots[i]
        used = {vol[j] for j in range(nd) if j != i and slots[j] == pair}
        c = rng.randrange(m)
        if c in used or c == vol[i]:
            continue
        old = vol[i]
        vol[i] = c
        v = _lift_unreached(m, slots, vol, T, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            vol[i] = old
    return vol if cur == 0 else None


def _lift_attempt(m, slots, d, D, rng, deadline):
    """Try groups of order m with voltages; return (n, edges) for a valid lift, or None."""
    groups = _groups(m)
    rng.shuffle(groups)
    for mm, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(mm, k, r)
        T = [[mul(x, g) for g in range(m)] for x in range(m)]
        vol = _lift_anneal(m, slots, T, D, rng, LIFT_ITERS, deadline)
        if vol is not None:
            darts = [(u, bidx, g) for (u, bidx), g in zip(slots, vol)]
            n, edges = lib.group_lift(4, darts, m, mul)
            return n, edges
    return None


def _lift_search(d, D, rng, deadline, best, consider):
    """Search two-orbit lifts with orders m above the current best (4m vertices)."""
    mmax = lib._moore_bound(d, D) // 4
    slot_sets = [_dart_slots(d, a) for a in range(1, d // 2 + 1)]
    if not slot_sets or max(2, best[0] // 4 + 1) > mmax:
        return
    budget = 1.0
    while time.monotonic() < deadline:
        improved = False
        for m in range(max(2, best[0] // 4 + 1), mmax + 1):
            if time.monotonic() >= deadline:
                break
            if 4 * m <= best[0]:
                continue
            for slots in slot_sets:
                now = time.monotonic()
                if now >= deadline:
                    break
                res = _lift_attempt(m, slots, d, D, rng, min(deadline, now + budget))
                if res is not None:
                    consider(*res)
                    improved = True
                    break
            if improved:
                break
        if not improved:
            budget *= 2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0] = n
            best[1] = e

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() - start < 0.05 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best[0], best[1]

    # Phase 1: quick bi-Cayley pass (one base vertex per side).
    _bicayley_search(d, D, rng, start + 0.2 * time_limit, consider)

    # Phase 2: two-orbit lifts over non-abelian groups, aiming above the best order.
    _lift_search(d, D, rng, start + 0.8 * time_limit, best, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
