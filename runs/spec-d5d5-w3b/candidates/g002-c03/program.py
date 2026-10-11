import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

MAX_GROUPS = 10        # groups tried per bi-Cayley order N
CLIMB_ITERS = 400      # annealing steps per (group, connection set) try
RESTARTS = 2           # random restarts of the connection set per group
ANNEAL_ITERS = 800     # annealing steps for multi-base lifts
SWEEP_WINDOW = 12      # bi-Cayley orders swept above the lower bound before resetting
SA_ITERS = 5000        # edge-switch annealing steps per attempt (new method)
_BIG = 10 ** 9
_TABLE_CACHE = {}
_TABLE_CACHE_CAP = 12  # tables are N x N, so keep the cache small


# ----------------------------------------------------------------------------
# Structured baselines (projective plane for D = 3, generalized quadrangle for D = 4).
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
# NEW METHOD: simulated annealing over edge switches on d-regular bipartite
# graphs with parts A = 0..M-1 and B = M..2M-1. The cost is the number of
# ordered vertex pairs at distance > D. Every switch keeps degrees and
# bipartiteness, and the cost is recomputed exactly with bitset balls.
# ----------------------------------------------------------------------------

def _bad_count(N, adj, D):
    """Ordered pairs (u, v) with distance > D, for adjacency sets adj on N vertices."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        if new == reach:
            break
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _circulant_bip(M, d):
    """Simple d-regular bipartite start: A_i ~ B_{i+s mod M} for s = 0..d-1 (needs M >= d)."""
    adj = [set() for _ in range(2 * M)]
    edges = []
    for i in range(M):
        for s in range(d):
            j = (i + s) % M
            adj[i].add(M + j)
            adj[M + j].add(i)
            edges.append([i, M + j])
    return adj, edges


def _try_switch(adj, edges, rng):
    """Pick two edges (a1,b1), (a2,b2); return indices if the switch to (a1,b2), (a2,b1) is legal."""
    i = rng.randrange(len(edges))
    j = rng.randrange(len(edges))
    if i == j:
        return None
    a1, b1 = edges[i]
    a2, b2 = edges[j]
    if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
        return None
    return i, j


def _apply_switch(adj, edges, i, j):
    """Replace (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Applying it again with the same indices undoes it."""
    a1, b1 = edges[i]
    a2, b2 = edges[j]
    adj[a1].discard(b1)
    adj[b1].discard(a1)
    adj[a2].discard(b2)
    adj[b2].discard(a2)
    adj[a1].add(b2)
    adj[b2].add(a1)
    adj[a2].add(b1)
    adj[b1].add(a2)
    edges[i] = [a1, b2]
    edges[j] = [a2, b1]


def _sa_regular(M, d, D, rng, deadline, iters):
    """Anneal a d-regular bipartite graph on 2M vertices to diameter <= D. Returns edge list or None."""
    N = 2 * M
    adj, edges = _circulant_bip(M, d)
    for _ in range(2 * len(edges)):
        p = _try_switch(adj, edges, rng)
        if p is not None:
            _apply_switch(adj, edges, *p)
    cur = _bad_count(N, adj, D)
    T0 = max(2.0, 0.01 * cur)
    T1 = 0.3
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        p = _try_switch(adj, edges, rng)
        if p is None:
            continue
        temp = T0 * (T1 / T0) ** (it / iters)
        _apply_switch(adj, edges, *p)
        new = _bad_count(N, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = new
        else:
            _apply_switch(adj, edges, *p)
    if cur == 0:
        return [(a, b) for a, b in edges]
    return None


def _sa_search(d, D, rng, deadline, best_n, moore):
    """Grow the order by one bipartite pair at a time, each attempt annealed from scratch."""
    best = None
    M = max(d, best_n // 2 + 1)
    while time.monotonic() < deadline and 2 * M <= moore:
        edges = _sa_regular(M, d, D, rng, deadline, SA_ITERS)
        if edges is None:
            continue
        best = (2 * M, edges)
        M += 1
    return best


# ----------------------------------------------------------------------------
# LEGACY METHOD (kept as a safe fallback): bi-Cayley lifts over Z_m x|_r Z_k
# and multi-base voltage lifts over semidirect products, annealed.
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


def _right_perm(mul, G, s):
    """Permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    """Edge list of the lift, A-vertices first, B-vertices after."""
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    temp = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(T_end, temp * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def _legacy_search(d, D, rng, deadline, best_n, moore):
    """Bi-Cayley and multi-base lifts; returns the best (n, edges) found above best_n, or None."""
    best = None
    bicayley_prob = 0.7 if D >= 4 else 0.5
    sweep = None
    while best_n < moore and time.monotonic() < deadline:
        if d >= 2 and rng.random() < bicayley_prob:
            lo = best_n // 2 + 1
            if lo > moore // 2:
                break
            if sweep is None or sweep < lo or sweep > lo + SWEEP_WINDOW:
                sweep = lo
            N = sweep
            sweep += 1
            found = _bicayley_search(N, d, D, rng, deadline)
            if found is not None:
                T, S = found
                cand = (2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
                if cand[0] > best_n:
                    best, best_n = cand, cand[0]
        else:
            k = rng.choice((2, 3))
            lo = best_n // (2 * k) + 1
            if 2 * k * lo > moore:
                continue
            G = lo + rng.randrange(max(2, lo // 10))
            m, k2, r = rng.choice(_groups(G))
            order, mul, _ = lib.semidirect_group(m, k2, r)
            res = _anneal(d, D, k, order, mul, rng, deadline, ANNEAL_ITERS)
            if res is not None and res[0] > best_n:
                best, best_n = res, res[0]
    return best


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

    # Safe fallback: K_{d,d} has diameter 2 and meets the Moore bound 2d for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    if D == 3:
        consider(_best_pg(d))
        if best[0] >= moore:
            return best
    if D == 4:
        consider(_best_gq(d))
        if best[0] >= moore:
            return best

    # For D >= 4 and d >= 3, split time: the legacy lifts secure a strong baseline first,
    # then the edge-switch annealer tries to exceed it.
    use_sa = d >= 3 and D >= 4
    legacy_end = start + (0.5 * budget if use_sa else budget)
    consider(_legacy_search(d, D, rng, legacy_end, best[0], moore))

    if use_sa and best[0] < moore and time.monotonic() < deadline:
        sa_rng = random.Random(seed * 1000003 + d * 101 + D)
        res = _sa_search(d, D, sa_rng, deadline, best[0], moore)
        if res is not None:
            consider(res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
