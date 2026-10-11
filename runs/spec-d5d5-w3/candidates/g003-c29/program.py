import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Tunables
# ----------------------------------------------------------------------------

MAX_GROUPS = 12        # groups tried per side-size N in one bi-Cayley attempt
CLIMB_ITERS = 1200     # hill-climb steps per restart
STALL_LIMIT = 250      # re-randomize after this many non-improving steps
WINDOW = 6             # bi-Cayley side sizes tried just above the current best
PHASE1_FRAC = 0.35     # share of the budget for the bi-Cayley seed search
ANNEAL_T0 = 4.0
ANNEAL_T1 = 0.1
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# Structured baselines (D = 3 and D = 4 families).
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5 for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k: used to seed a large near-regular graph.
# A_x ~ B_{x g} for g in S, |S| = d. Identity is WLOG in S.
# ----------------------------------------------------------------------------

def _groups(N):
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (T, invs)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D, cap=None):
    """Count (source, vertex) pairs not within distance D, sources A_0 and B_0."""
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
        if cap is not None and total > cap:
            return total
    return total


def _climb(N, T, invs, d, D, rng, iters, deadline):
    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, _unreached(N, T, invs, S, D)

    S, cur = fresh()
    stall = 0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D, cap=cur)
        if v < cur:
            stall = 0
        else:
            stall += 1
        if v <= cur:
            S, cur = S2, v
        if stall > STALL_LIMIT:
            S, cur = fresh()
            stall = 0
    return S if cur == 0 else None


def _search_bicayley(d, D, N, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k2, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        T, invs = _tables(m, k2, r)
        S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
        if S is not None:
            return [(x, T[x][g]) for x in range(N) for g in S]
    return None


# ----------------------------------------------------------------------------
# Bold phase: grow a near-regular bipartite graph one side-vertex at a time.
# Representation: E is a list of (a, b) with a in 0..N-1 (side A), b in 0..N-1 (side B).
# Insertion keeps every degree at d; simulated annealing with double-edge swaps
# then repairs the diameter defects.
# ----------------------------------------------------------------------------

def _to_E(n, edges):
    """Convert a bipartite (n, edges) with sides [0, n/2) and [n/2, n) to (N, E)."""
    N = n // 2
    E = []
    for u, v in edges:
        if u > v:
            u, v = v, u
        if not (u < N <= v):
            return None
        E.append((u, v - N))
    return N, E


def _to_edges(N, E):
    return 2 * N, [(a, N + b) for a, b in E]


def _cost_E(N, E, D):
    """Number of ordered (source, vertex) pairs not reached within D. Zero means valid."""
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _insert(N, E, d, rng):
    """Add A-vertex N and B-vertex N by rewiring d edges with distinct endpoints."""
    order = E[:]
    rng.shuffle(order)
    usedx, usedy, chosen = set(), set(), []
    for x, y in order:
        if x in usedx or y in usedy:
            continue
        usedx.add(x)
        usedy.add(y)
        chosen.append((x, y))
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    chosen_set = set(chosen)
    newE = [e for e in E if e not in chosen_set]
    for x, y in chosen:
        newE.append((x, N))   # old A-vertex x now sees new B-vertex N
        newE.append((N, y))   # new A-vertex N now sees old B-vertex y
    return newE


def _anneal(N, E, d, D, rng, deadline):
    """Double-edge-swap annealing on a d-regular bipartite graph (N per side)."""
    E = list(E)
    S = set(E)
    cur = _cost_E(N, E, D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = ANNEAL_T0 * (ANNEAL_T1 / ANNEAL_T0) ** min(1.0, (now - start) / span)
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        c2 = _cost_E(N, E, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
            S.discard((a1, b1))
            S.discard((a2, b2))
            S.add((a1, b2))
            S.add((a2, b1))
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return E if cur == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    base = lib.haar_graph(d, range(d))   # K_{d,d}: optimal for D = 2
    if D == 2:
        return base

    best = base
    best_n = base[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Structured baselines; D = 3 with d-1 a prime power is already optimal.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Phase 1: seed with a bi-Cayley lift near the current best order.
    phase1_deadline = start + PHASE1_FRAC * budget
    while time.monotonic() < phase1_deadline and best_n < lib.moore_bound(d, D):
        lo = best_n // 2 + 1
        N = lo + rng.randrange(WINDOW)
        if N <= d:
            N = d + 1
        E = _search_bicayley(d, D, N, rng, phase1_deadline)
        if E is not None:
            consider(2 * N, [(a, N + b) for a, b in E])

    # Phase 2: grow the best graph by insertion + annealing, one side-vertex at a time.
    conv = _to_E(*best)
    if conv is not None:
        Nside, E = conv
        while time.monotonic() < deadline:
            if 2 * (Nside + 1) > lib.moore_bound(d, D):
                break
            newE = _insert(Nside, E, d, rng)
            if newE is None:
                continue
            res = _anneal(Nside + 1, newE, d, D, rng, deadline)
            if res is None:
                break
            Nside += 1
            E = res
            consider(*_to_edges(Nside, E))

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
