import itertools
import math
import random
import time

import lib

MAX_GROUPS = 8        # groups tried per lift attempt
LIFT_ITERS = 1200     # annealing steps per (group, base) try
PARENT_FRAC = 0.35    # share of the time budget spent on the bi-Cayley phase
ITERS = 400           # annealing steps per bi-Cayley try
MAX_GROUPS_PARENT = 12
SAFETY = 0.85         # fraction of time_limit we allow ourselves


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
# Bi-Cayley search over semidirect products (phase 1, the parent's method).
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
    for m, k, r in groups[:MAX_GROUPS_PARENT]:
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
# Phase 2 (new): voltage lifts of small bipartite base multigraphs with t
# vertices per side (t = 2 or 3), d-regular base, over a semidirect group of
# order N. Vertex count is 2tN. Left multiplication is an automorphism, so
# eccentricities only need to be checked from the base representatives (u, e).
# ----------------------------------------------------------------------------

def _lift_adj(t, N, T, darts):
    """Adjacency lists of the lift. A block u occupies u*N.., B block v occupies (t+v)*N.."""
    V = 2 * t * N
    adj = [[] for _ in range(V)]
    for u, v, g in darts:
        ub = u * N
        bb = (t + v) * N
        for x in range(N):
            a = ub + x
            b = bb + T[x][g]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _lift_cost(adj, t, N, D):
    """Total number of (base representative, vertex) pairs at distance > D."""
    V = len(adj)
    total = 0
    for s in range(2 * t):
        src = s * N
        seen = bytearray(V)
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
        total += V - count
    return total


def _lift_anneal(t, N, T, base, D, rng, iters, deadline):
    """Anneal the voltages of the darts in base (list of (u, v)) to zero the cost."""
    darts = [[u, v, rng.randrange(N)] for u, v in base]
    cur = _lift_cost(_lift_adj(t, N, T, darts), t, N, D)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        i = rng.randrange(len(darts))
        old = darts[i][2]
        new = rng.randrange(N)
        if new == old:
            continue
        darts[i][2] = new
        v2 = _lift_cost(_lift_adj(t, N, T, darts), t, N, D)
        temp = max(0.2, 2.0 * (1.0 - it / iters))
        if v2 <= cur or rng.random() < math.exp(-(v2 - cur) / temp):
            cur = v2
        else:
            darts[i][2] = old
    return darts if cur == 0 else None


def _lift_attempt(t, N, d, D, rng, deadline):
    """Try groups of order N with random d-regular base multigraphs on t+t vertices."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        # Base: d layers, each a permutation matching A-side to B-side,
        # giving a d-regular bipartite multigraph on t + t vertices.
        base = []
        for _ in range(d):
            perm = list(range(t))
            rng.shuffle(perm)
            for u in range(t):
                base.append((u, perm[u]))
        darts = _lift_anneal(t, N, T, base, D, rng, LIFT_ITERS, deadline)
        if darts is not None:
            return T, darts
    return None


def _lift_edges(t, N, T, darts):
    """Materialize the lift as (n, edges)."""
    edges = set()
    for u, v, g in darts:
        for x in range(N):
            a = u * N + x
            b = (t + v) * N + T[x][g]
            edges.add((min(a, b), max(a, b)))
    return 2 * t * N, sorted(edges)


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def _consider(state, d, D, n, e):
    """Replace the stored best if (n, e) is larger and passes the exact validity check."""
    if n > state[0][0] and lib.is_valid(n, e, d, D):
        state[0] = (n, e)


def _bicayley_phase(d, D, rng, deadline, state):
    """Parent's bi-Cayley search, used as a safe first phase."""
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
            res = _attempt(N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            _consider(state, d, D, 2 * N, edges)
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 2


def _lift_phase(d, D, rng, deadline, state):
    """New phase: search voltage lifts of t+t vertex base graphs, aiming above the current best."""
    moore = lib._moore_bound(d, D)
    cands = []
    for t in (2, 3):
        hi = moore // (2 * t)
        for N in range(max(2, state[0][0] // (2 * t)), hi + 1):
            n = 2 * t * N
            if state[0][0] < n <= moore:
                cands.append((n, t, N))
    cands.sort()
    cands = cands[:80]
    if not cands:
        return
    budget = 0.5
    while time.monotonic() < deadline:
        success = False
        for n, t, N in cands:
            if time.monotonic() >= deadline:
                break
            if n <= state[0][0]:
                continue
            now = time.monotonic()
            res = _lift_attempt(t, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, darts = res
            nn, e = _lift_edges(t, N, T, darts)
            _consider(state, d, D, nn, e)
            success = True
            break
        if not success:
            budget *= 2
            if budget > 60:
                break


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + SAFETY * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    state = [(1, [])]

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        _consider(state, d, D, n, e)
        return state[0]

    # Cheap baselines first, always valid when they pass lib.is_valid.
    if D >= 2:
        _consider(state, d, D, *lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            _consider(state, d, D, pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            _consider(state, d, D, gq[0], gq[1])

    if d < 2 or D < 2:
        return state[0]

    # Phase 1: parent's bi-Cayley search gives a safe level of quality.
    phase1_end = start + PARENT_FRAC * SAFETY * time_limit
    _bicayley_phase(d, D, rng, min(phase1_end, deadline), state)

    # Phase 2: the new multi-vertex base lift search, aiming above the phase-1 best.
    if time.monotonic() < deadline:
        _lift_phase(d, D, rng, deadline, state)

    n, e = state[0]
    if not lib.is_valid(n, e, d, D):
        return 1, []
    return n, e
