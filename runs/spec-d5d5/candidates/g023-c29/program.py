import itertools
import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# Tunables.
# Phase 1 (new): bipartite base graphs with b vertices per side, lifted over
#                semidirect groups Z_m x| Z_k. Order = 2*b*N.
# Phase 2 (fallback): the bi-Cayley search (b = 1) from the parent program.
# ----------------------------------------------------------------------------
LIFT_FRACTION = 0.55      # share of time_limit given to the lift search
TOTAL_FRACTION = 0.80     # overall deadline share
LIFT_ITERS = 800          # annealing steps per (group, base graph) try
LIFT_GROUPS = 12          # groups tried per attempt
LIFT_SLICE = 3.0          # seconds per random (b, N) attempt
LIFT_WINDOW = 60          # only orders in (best, best + window] are targeted
LIFT_MAX_B = 5            # base graph sizes per side

MAX_GROUPS_PER_ATTEMPT = 30   # parent bi-Cayley: groups tried per order N
ITERS = 800                   # parent bi-Cayley: annealing steps
TOP_SLACK = 8                 # parent bi-Cayley: search orders up to Nmax//2 + slack


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


def _group_tables(N, m, k, r):
    """Return (T, ginv): T[x][g] = x*g and ginv[g] = g^{-1}; identity is element 0."""
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    ginv = [inv(g) for g in range(N)]
    return T, ginv


# ----------------------------------------------------------------------------
# NEW: lifts of bipartite base graphs with b vertices per side over a group G.
#
# Vertices: A_{i,x} = i*N + x, B_{j,y} = b*N + j*N + y, for i, j < b and x, y in G.
# A dart (i, j, g) gives edges A_{i,x} -- B_{j, x*g} for all x.
# Each A_i has exactly d darts out and each B_j exactly d darts in; all darts
# distinct, so the lift is simple and d-regular. Left multiplication is an
# automorphism, so the diameter is decided by the 2b sources A_{i,e}, B_{j,e}.
# ----------------------------------------------------------------------------

def _lift_cost(b, N, d, D, T, ginv, darts):
    """Number of (source, vertex) pairs at distance > D over the 2b representative sources."""
    bN = b * N
    V = 2 * bN
    out = [[] for _ in range(b)]
    inn = [[] for _ in range(b)]
    for i, j, g in darts:
        out[i].append((j, g))
        inn[j].append((i, ginv[g]))
    total = 0
    sources = [i * N for i in range(b)] + [bN + j * N for j in range(b)]
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < bN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in out[i]:
                        v = bN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - bN, N)
                    row = T[y]
                    for i, h in inn[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _lift_anneal(b, N, d, D, T, ginv, rng, iters, deadline):
    """Anneal darts so that the lift has diameter <= D. Returns darts or None."""
    nd = b * d
    slots = [j for j in range(b) for _ in range(d)]
    rng.shuffle(slots)
    darts = []
    used = set()
    for k in range(nd):
        i = k // d
        j = slots[k]
        while True:
            g = rng.randrange(N)
            if (i, j, g) not in used:
                break
        used.add((i, j, g))
        darts.append((i, j, g))

    cur = _lift_cost(b, N, d, D, T, ginv, darts)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        k = rng.randrange(nd)
        new = list(darts)
        if b == 1 or rng.random() < 0.5:
            i, j, _ = darts[k]
            new[k] = (i, j, rng.randrange(N))
        else:
            k2 = rng.randrange(nd)
            i1, j1, g1 = darts[k]
            i2, j2, g2 = darts[k2]
            if i1 == i2 or j1 == j2:
                continue
            new[k] = (i1, j2, g1)
            new[k2] = (i2, j1, g2)
        if len(set(new)) != nd:
            continue
        v = _lift_cost(b, N, d, D, T, ginv, new)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = new, v
    return darts if cur == 0 else None


def _lift_attempt(b, N, d, D, rng, deadline):
    """Try groups of order N for base size b. Returns (T, darts) or None."""
    if N < d:
        return None
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:LIFT_GROUPS]:
        if time.monotonic() > deadline:
            return None
        T, ginv = _group_tables(N, m, k, r)
        darts = _lift_anneal(b, N, d, D, T, ginv, rng, LIFT_ITERS, deadline)
        if darts is not None:
            return T, darts
    return None


def _lift_edges(b, N, T, darts):
    """Expand darts into the edge list of the lift; returns (n, edges)."""
    bN = b * N
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, bN + j * N + T[x][g]))
    return 2 * bN, edges


def _lift_phase(d, D, rng, deadline, consider, state):
    """Randomly sample (b, N) with orders just above the current best, and anneal."""
    moore = lib._moore_bound(d, D)
    while time.monotonic() < deadline:
        lo = state["n"] + 1
        hi = min(state["n"] + LIFT_WINDOW, moore)
        cands = []
        for b in range(1, LIFT_MAX_B + 1):
            for N in range(max(d + 1, -(-lo // (2 * b))), hi // (2 * b) + 1):
                if lo <= 2 * b * N <= hi:
                    cands.append((b, N))
        if not cands:
            break
        b, N = rng.choice(cands)
        res = _lift_attempt(b, N, d, D, rng, min(deadline, time.monotonic() + LIFT_SLICE))
        if res is not None:
            T, darts = res
            n, e = _lift_edges(b, N, T, darts)
            consider(n, e)


# ----------------------------------------------------------------------------
# Fallback: bi-Cayley search over semidirect products (parent's method, b = 1).
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


def _bicayley_anneal(N, T, invs, d, D, rng, iters, deadline):
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


def _bicayley_attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a connection set with diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _bicayley_anneal(N, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _bicayley_phase(d, D, rng, deadline, consider):
    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
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
            res = _bicayley_attempt(N, d, D, rng, att_deadline)
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


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    state = {"n": 1, "e": []}

    def consider(n, e):
        if n > state["n"] and lib.is_valid(n, e, d, D):
            state["n"] = n
            state["e"] = e

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return state["n"], state["e"]

    # Safe baselines.
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
        return state["n"], state["e"]

    # Phase 1: new construction (multi-vertex base graphs lifted over groups).
    _lift_phase(d, D, rng, start + LIFT_FRACTION * time_limit, consider, state)

    # Phase 2: fallback bi-Cayley search for whatever time remains.
    _bicayley_phase(d, D, rng, start + TOTAL_FRACTION * time_limit, consider)

    if not lib.is_valid(state["n"], state["e"], d, D):
        return 1, []
    return state["n"], state["e"]
