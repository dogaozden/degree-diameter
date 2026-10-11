import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured baselines: projective planes (D = 3) and generalized quadrangles (D = 4).
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k with a hill-climb on the connection set.
# Every such graph is d-regular and bipartite with sides A = [0, N), B = [N, 2N).
# ----------------------------------------------------------------------------

MAX_GROUPS = 8
CLIMB_ITERS = 300
BAND_EXTRA = 12
ANNEAL_T0 = 2.0
ANNEAL_T1 = 0.05
_TABLE_CACHE = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
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
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Count (source, target) pairs not within distance D, from A_0 and B_0."""
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
    """Hill-climb a connection set S (identity fixed as one dart) to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur:
            S, cur = S2, v
    return S if cur == 0 else None


def _bicayley_phase(d, D, moore, rng, deadline, n_best):
    """Sweep bi-Cayley orders upward; return (n, edges, isA) of the largest valid one found, or None."""
    found_struct = None
    cur_best = n_best
    sweep = None
    while time.monotonic() < deadline and cur_best < moore:
        lo = cur_best // 2 + 1
        if lo > moore // 2:
            break
        if sweep is None or sweep < lo or sweep > lo + BAND_EXTRA:
            sweep = lo
        N = sweep
        sweep += 1
        groups = _groups(N)
        rng.shuffle(groups)
        hit = None
        for m, k, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            _, _, T, invs = _tables(m, k, r)
            S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
            if S is not None:
                hit = (T, S)
                break
        if hit is not None:
            T, S = hit
            E = [(x, N + T[x][g]) for x in range(N) for g in S]
            n2 = 2 * N
            if len(set(E)) == len(E) and lib.is_valid(n2, E, d, D):
                isA = [True] * N + [False] * N
                found_struct = (n2, E, isA)
                cur_best = n2
    return found_struct


# ----------------------------------------------------------------------------
# Bold step: grow a regular bipartite graph by two vertices (one per side) and
# repair the diameter with simulated annealing over degree-preserving 2-switches.
# ----------------------------------------------------------------------------

def _bad_pairs_fast(n, adj, D):
    """Number of ordered (v, w) pairs with dist > D, via bitmask balls."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _insert_and_anneal(n, E, isA, d, D, deadline, rng):
    """Insert vertices x (side A) and y (side B) and anneal to diameter D.

    Returns (n + 2, edges, isA) with diameter <= D, or None if time runs out.
    """
    el = [(a, b) if isA[a] else (b, a) for a, b in E]
    deg = [0] * n
    for a, b in el:
        deg[a] += 1
        deg[b] += 1
    if any(x != d for x in deg):
        return None

    x, y = n, n + 1
    isA2 = list(isA) + [True, False]

    # Pick d edges with pairwise distinct A-ends and distinct B-ends; rewire them.
    order = list(range(len(el)))
    rng.shuffle(order)
    usedA, usedB, picked = set(), set(), []
    for i in order:
        a, b = el[i]
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        picked.append(i)
        if len(picked) == d:
            break
    if len(picked) < d:
        return None

    pset = set(picked)
    E_list = [el[i] for i in range(len(el)) if i not in pset]
    for i in picked:
        a, b = el[i]
        E_list.append((x, b))   # A-side x to B-side b
        E_list.append((a, y))   # A-side a to B-side y

    N2 = n + 2
    adj = [set() for _ in range(N2)]
    for a, b in E_list:
        adj[a].add(b)
        adj[b].add(a)

    cost = _bad_pairs_fast(N2, adj, D)
    t_start = time.monotonic()
    span = max(1e-9, deadline - t_start)
    M = len(E_list)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = min(1.0, (now - t_start) / span)
        T = ANNEAL_T0 * (ANNEAL_T1 / ANNEAL_T0) ** frac

        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E_list[i]
        c, e = E_list[j]
        if a == c or b == e:
            continue
        if e in adj[a] or b in adj[c]:
            continue

        # Apply the 2-switch: (a,b),(c,e) -> (a,e),(c,b).
        adj[a].remove(b)
        adj[b].remove(a)
        adj[c].remove(e)
        adj[e].remove(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)

        new = _bad_pairs_fast(N2, adj, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
            E_list[i] = (a, e)
            E_list[j] = (c, b)
        else:
            adj[a].remove(e)
            adj[e].remove(a)
            adj[c].remove(b)
            adj[b].remove(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)

    return N2, E_list, isA2


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

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Phase 1: bi-Cayley search for a regular base graph.
    struct = None
    if best[0] < moore:
        struct = _bicayley_phase(d, D, moore, rng, start + 0.5 * budget, best[0])
        if struct is not None:
            consider(struct[0], struct[1])

    # Phase 2: repeated insertion-and-anneal growth on the regular base.
    while struct is not None and best[0] < moore and time.monotonic() < deadline:
        grown = _insert_and_anneal(struct[0], struct[1], struct[2], d, D, deadline, rng)
        if grown is None:
            break
        if not lib.is_valid(grown[0], grown[1], d, D):
            break
        consider(grown[0], grown[1])
        struct = grown

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
