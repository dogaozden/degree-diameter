import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

MAX_GROUPS = 10       # groups tried per bi-Cayley order N
CLIMB_ITERS = 400     # annealing steps per (group, connection set) try
RESTARTS = 2          # random restarts of the connection set per group
_BIG = 10 ** 9
_TABLE_CACHE = {}
_TABLE_CACHE_CAP = 12  # tables are N x N, so keep the cache small

P1_FRACTION = 0.5     # share of the budget for the bi-Cayley sweep (phase 1)


# ----------------------------------------------------------------------------
# Structured baselines: projective planes, quadrangles, Araujo-Pardo-Lopez.
# These are the safe fallbacks for D = 3 and D = 4.
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
# Bi-Cayley lifts over Z_m x|_r Z_k with an annealed connection set.
# Vertices A_x and B_y (x, y in G). Edge A_x -- B_{x s} for s in S, |S| = d.
# The result is d-regular bipartite; it seeds the switch-annealing phase.
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


def _tables(m, k, r):
    """Cached (order, mul, T, invs) for Z_m x|_r Z_k, where T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= _TABLE_CACHE_CAP:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Count vertex pairs (source, target) not within distance D, from A_0 and B_0."""
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


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Anneal a connection set S (identity fixed in S) to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        temp = 0.3 + 1.5 * (1.0 - it / iters)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _bicayley_search(N, d, D, rng, deadline):
    """Try groups of order N with restarts; return (T, S) on success, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        _, _, T, invs = _tables(m, k, r)
        for _ in range(RESTARTS):
            if time.monotonic() > deadline:
                break
            S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
            if S is not None:
                return T, S
    return None


# ----------------------------------------------------------------------------
# Bold change: d-regular bipartite graphs on N + N vertices, improved by
# degree-preserving edge switches under simulated annealing. The cost is the
# number of unordered vertex pairs at distance > D.
#
# Growth: insert one A-vertex and one B-vertex by rerouting a matching of d
# edges through the new pair (keeps d-regularity), then anneal switches back
# to zero cost. Local indices: A vertex i is i, B vertex j is N + j globally.
# ----------------------------------------------------------------------------

def _bad_pairs(N, E, D):
    """Number of unordered pairs at distance > D in the bipartite graph with edges E (local indices)."""
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _switch_anneal(N, d, D, E, rng, t_end):
    """Anneal degree-preserving switches on E to zero bad pairs before t_end. Returns E or None."""
    E = list(E)
    eset = set(E)
    m = len(E)
    cost = _bad_pairs(N, E, D)
    if cost == 0:
        return E
    t_start = time.monotonic()
    span = max(1e-3, t_end - t_start)
    T0 = 0.5 + 0.02 * cost
    T1 = 0.15
    temp = T0
    it = 0
    while cost > 0:
        it += 1
        if (it & 7) == 0:
            now = time.monotonic()
            if now >= t_end:
                break
            frac = (now - t_start) / span
            temp = T0 * (T1 / T0) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        eset.discard((a1, b1))
        eset.discard((a2, b2))
        eset.add((a1, b2))
        eset.add((a2, b1))
        c2 = _bad_pairs(N, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            eset.discard((a1, b2))
            eset.discard((a2, b1))
            eset.add((a1, b1))
            eset.add((a2, b2))
    return E if cost == 0 else None


def _insert_pair(N, d, E, rng):
    """Add one A-vertex and one B-vertex (local index N), keeping d-regularity.

    A matching of d edges (a_i, b_i) is removed; the new A-vertex joins every b_i and
    the new B-vertex joins every a_i. Returns (N + 1, new edge list) or None.
    """
    order = list(range(len(E)))
    rng.shuffle(order)
    usedA = set()
    usedB = set()
    pick = []
    for idx in order:
        a, b = E[idx]
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        pick.append(idx)
        if len(pick) == d:
            break
    if len(pick) < d:
        return None
    picked = set(pick)
    newE = [E[i] for i in range(len(E)) if i not in picked]
    for idx in pick:
        a, b = E[idx]
        newE.append((N, b))
        newE.append((a, N))
    return N + 1, newE


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and meets the Moore bound 2d for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baselines.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        q = d - 2
        if q >= 3 and lib.is_prime_power(q) and best[0] < moore:
            try:
                ar = lib.araujo_lopez_graph(q)
                consider(ar[0], ar[1])
            except Exception:
                pass
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best[0] >= moore:
        return best

    moore_n = moore // 2  # maximum order per side

    # ---------------- Phase 1: bi-Cayley sweep (secures a regular seed graph).
    state = None  # (N, E) with E d-regular, valid for diameter D
    if d >= 2:
        p1_end = start + P1_FRACTION * budget
        N = max(d, best[0] // 2 + 1)
        while N <= moore_n and time.monotonic() < p1_end:
            found = _bicayley_search(N, d, D, rng, p1_end)
            if found is not None:
                T, S = found
                E = [(x, T[x][g]) for x in range(N) for g in S]
                state = (N, E)
                consider(2 * N, [(a, N + b) for a, b in E])
            N += 1

    # ---------------- Phase 2: insertion growth with switch annealing.
    if state is None:
        N0 = max(d, moore_n // 4)
        E0 = [(a, (a + s) % N0) for a in range(N0) for s in range(d)]
        now = time.monotonic()
        t_end = min(deadline, now + max(3.0, 0.2 * (deadline - now)))
        res = _switch_anneal(N0, d, D, E0, rng, t_end)
        if res is not None:
            state = (N0, res)
            consider(2 * N0, [(a, N0 + b) for a, b in res])

    fails = 0
    while state is not None and time.monotonic() < deadline:
        N, E = state
        if 2 * (N + 1) > moore:
            break
        ins = _insert_pair(N, d, E, rng)
        if ins is None:
            break
        N1, E1 = ins
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.5:
            break
        slice_end = now + min(remaining, max(4.0, 0.25 * remaining))
        res = _switch_anneal(N1, d, D, E1, rng, slice_end)
        if res is not None:
            state = (N1, res)
            consider(2 * N1, [(a, N1 + b) for a, b in res])
            fails = 0
        else:
            fails += 1
            if fails >= 3:
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
