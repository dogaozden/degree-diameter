import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per order N within one attempt
ITERS = 600                   # annealing steps per (group, connection set) try
T_HOT = 1.5                   # initial annealing temperature (in unreached-pair units)
T_COLD = 0.15                 # final annealing temperature

LIFT_ITERS = 400              # annealing steps per voltage-lift attempt
LIFT_GROUPS_PER_ORDER = 4     # groups tried per (total order, base size) pair
LIFT_START_ORDER = 338        # first total order beyond the known record 336
LIFT_BASE_SIZES = (2, 3, 4)   # base graphs with a+a vertices, 5-regular


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
# Shared group enumeration: semidirect products Z_m x|_r Z_k of order N.
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
# NEW: voltage lifts over a small bipartite base with a+a vertices and 5 darts
# per base vertex, voltages in a finite group G of order m.
#
# Vertices: A(i, x) = i*m + x, B(j, y) = a*m + j*m + y.
# For each t in 0..4 and base vertex i: A(i, x) -- B(perm_t[i], x * g_{t,i}).
# Left multiplication by G is an automorphism, so distances from the base
# representatives A(i, e), B(j, e) determine the diameter.
# Total order is 2*a*m; orders above the record 336 are targeted.
# ----------------------------------------------------------------------------

def _group_table(mm, k, r):
    """Multiplication table of Z_mm x|_r Z_k as a list of lists."""
    order, mul, _ = lib.semidirect_group(mm, k, r)
    return [[mul(x, g) for g in range(order)] for x in range(order)]


def _build_adj(a, m, perms, volt, M):
    """Adjacency lists of the lift (duplicate edges removed)."""
    V = 2 * a * m
    off = a * m
    adj = [[] for _ in range(V)]
    seen = set()
    for t in range(len(perms)):
        pt = perms[t]
        vt = volt[t]
        for i in range(a):
            j = pt[i]
            g = vt[i]
            base_u = i * m
            base_v = off + j * m
            for x in range(m):
                u = base_u + x
                v = base_v + M[x][g]
                key = u * V + v
                if key in seen:
                    continue
                seen.add(key)
                adj[u].append(v)
                adj[v].append(u)
    return adj


def _lift_cost(adj, V, sources, D):
    """Total number of (source, vertex) pairs not within distance D."""
    total = 0
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
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


def _lift_attempt(cand, rng, deadline, cache, D):
    """Anneal voltages for one (order, base size, group). Return (n, edges) on success, else None."""
    T, a, m, (mm, k, r) = cand
    key = (mm, k, r)
    M = cache.get(key)
    if M is None:
        M = _group_table(mm, k, r)
        cache[key] = M

    perms = [rng.sample(range(a), a) for _ in range(5)]
    V = 2 * a * m
    sources = [i * m for i in range(a)] + [a * m + j * m for j in range(a)]
    volt = [[rng.randrange(m) for _ in range(a)] for _ in range(5)]
    adj = _build_adj(a, m, perms, volt, M)
    cur = _lift_cost(adj, V, sources, D)

    for it in range(LIFT_ITERS):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / LIFT_ITERS)
        t = rng.randrange(5)
        i = rng.randrange(a)
        new = rng.randrange(m)
        old = volt[t][i]
        if new == old:
            continue
        volt[t][i] = new
        adj2 = _build_adj(a, m, perms, volt, M)
        v = _lift_cost(adj2, V, sources, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
            adj = adj2
        else:
            volt[t][i] = old

    if cur != 0:
        return None
    edges = [(u, v) for u in range(V) for v in adj[u] if u < v]
    return V, edges


def _lift_candidates(rng, Tmin, Tmax):
    """(T, a, m, group) tuples for totals T in [Tmin, Tmax], ascending in T."""
    cands = []
    for T in range(Tmin, Tmax + 1, 2):
        for a in LIFT_BASE_SIZES:
            if T % (2 * a):
                continue
            m = T // (2 * a)
            if m < 2:
                continue
            gs = _groups(m)
            rng.shuffle(gs)
            for g in gs[:LIFT_GROUPS_PER_ORDER]:
                cands.append((T, a, m, g))
    return cands


def _lift_search(d, D, rng, deadline):
    """Sweep voltage-lift candidates above the record; return (n, edges) or None."""
    Tmax = min(lib._moore_bound(d, D), 682)
    cands = _lift_candidates(rng, LIFT_START_ORDER, Tmax)
    cache = {}
    best = None
    best_n = 0
    budget = 0.6
    while time.monotonic() < deadline and cands:
        progressed = False
        for c in cands:
            if c[0] <= best_n:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            res = _lift_attempt(c, rng, min(deadline, now + budget), cache, D)
            if res is None:
                continue
            n, edges = res
            if n > best_n and lib.is_valid(n, edges, d, D):
                best_n = n
                best = (n, edges)
                progressed = True
                break
        if not progressed:
            budget = min(budget * 1.5, 6.0)
    return best


# ----------------------------------------------------------------------------
# Parent bi-Cayley search over semidirect products (fallback path).
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
    best_S, best_v = S, cur
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
            if cur < best_v:
                best_S, best_v = S[:], cur
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


def _parent_build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    if D >= 2 and d >= 1:
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

    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    top = min(Nmax, Nmax // 2 + 6)
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

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    if not (d == 5 and D == 5):
        return _parent_build(d, D, seed, time_limit)

    rng = random.Random(seed)
    best = (1, [])

    # Safe baseline first, so something valid is always available.
    base = lib.haar_graph(d, range(d))
    if lib.is_valid(base[0], base[1], d, D):
        best = base
    pg = _best_pg(d)
    if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
        best = pg

    # Bold path: voltage lifts over small non-cyclic bases, aimed above 336.
    lift_deadline = start + 0.55 * time_limit
    res = _lift_search(d, D, rng, lift_deadline)
    if res is not None and res[0] > best[0]:
        best = res

    # Parent fallback if the lift search did not beat the record.
    if best[0] <= 336:
        p = _parent_build(d, D, seed, 0.3 * time_limit)
        if p[0] > best[0] and lib.is_valid(p[0], p[1], d, D):
            best = p

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
