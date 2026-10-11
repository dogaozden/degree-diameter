import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per order N within one bi-Cayley attempt
ITERS = 800                   # annealing steps per (group, connection set) try
TOP_SLACK = 8                 # bi-Cayley orders up to Nmax//2 + TOP_SLACK

MAX_LIFT_GROUPS = 12          # groups tried per order N for the 2x2 voltage lift
LIFT_ITERS = 500              # annealing steps per (group, voltage assignment) try
OLD_PHASE_FRAC = 0.30         # fraction of the budget given to the bi-Cayley search


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
# Bold construction: 2x2 base voltage lift over a finite group.
#
# Base: A_0, A_1 (left) and B_0, B_1 (right). Dart (i, j, g) joins
# (A_i, x) to (B_j, x*g) for all x in G. Multiplicity matrix is
# [[p, d-p], [d-p, p]], so every vertex has degree d. Voltages on the same
# (i, j) pair are distinct, so the lift is simple. Left multiplication is an
# automorphism that is transitive on each fibre, so the four identity-vertex
# sources decide the diameter. Order is 4N, which beats 2N bi-Cayley graphs
# of the same group size.
# ----------------------------------------------------------------------------

def _lift_cost(N, T, darts, D):
    """Count (source, vertex) pairs at distance > D from the four fibre representatives."""
    V = 4 * N
    adj = [[] for _ in range(V)]
    for i, j, g in darts:
        base_a = i * N
        base_b = (2 + j) * N
        for x in range(N):
            u = base_a + x
            v = base_b + T[x][g]
            adj[u].append(v)
            adj[v].append(u)
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _lift_attempt(N, d, D, rng, deadline):
    """Search groups of order N and voltage assignments for a 2x2 lift of diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    patterns = list(range(1, d))  # p in 1..d-1 gives the matrix [[p, d-p], [d-p, p]]
    for m, k, r in groups[:MAX_LIFT_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        p = rng.choice(patterns)
        M = [[p, d - p], [d - p, p]]
        darts = []
        for i in range(2):
            for j in range(2):
                for g in rng.sample(range(N), M[i][j]):
                    darts.append((i, j, g))
        cur = _lift_cost(N, T, darts, D)
        for it in range(LIFT_ITERS):
            if cur == 0:
                return darts, T
            if time.monotonic() > deadline:
                break
            t = rng.randrange(len(darts))
            i, j, _ = darts[t]
            used = {g for (a, b, g) in darts if a == i and b == j}
            c = rng.randrange(N)
            if c in used:
                continue
            temp = max(0.05, 1.5 * (1.0 - it / LIFT_ITERS))
            new = darts[:]
            new[t] = (i, j, c)
            v = _lift_cost(N, T, new, D)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                darts, cur = new, v
        if cur == 0:
            return darts, T
    return None


def _lift_edges(N, darts, T):
    """Edges of the 4N-vertex lift: A_i ids i*N+x, B_j ids (2+j)*N+y."""
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, (2 + j) * N + T[x][g]))
    return edges


# ----------------------------------------------------------------------------
# Bi-Cayley search over semidirect products Z_m x| Z_k of order N (baseline).
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


def _bicayley_phase(d, D, rng, deadline, consider, best_n_fn):
    """Baseline bi-Cayley search, kept as a secondary family and safety net."""
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + TOP_SLACK)
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
            budget *= 1.5


def _lift_phase(d, D, rng, deadline, consider, best_n_fn):
    """Bold search: 2x2 base voltage lifts, aiming for orders above the current best."""
    Nmax4 = lib._moore_bound(d, D) // 4
    budget = 1.0
    while time.monotonic() < deadline:
        N = max(d + 1, best_n_fn() // 4 + 1)
        while N <= Nmax4 and time.monotonic() < deadline:
            att_deadline = min(deadline, time.monotonic() + budget)
            res = _lift_attempt(N, d, D, rng, att_deadline)
            if res is not None:
                darts, T = res
                consider(4 * N, _lift_edges(N, darts, T))
            N += 1
        if N > Nmax4 and best_n_fn() // 4 + 1 > Nmax4:
            break
        budget *= 2.0


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.85 * time_limit
    deadline = start + total
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

    def best_n_fn():
        return best_n

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

    if d >= 2 and D >= 2:
        # Baseline bi-Cayley search first (secures the record-level fallback).
        old_deadline = start + OLD_PHASE_FRAC * total
        _bicayley_phase(d, D, rng, old_deadline, consider, best_n_fn)

        # Bold 2x2 voltage-lift search for the remaining time.
        if time.monotonic() < deadline:
            _lift_phase(d, D, rng, deadline, consider, best_n_fn)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
