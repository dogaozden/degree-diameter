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
SPLICE_ITERS = 2500    # switch-annealing steps per splice attempt
MAIN_FRACTION = 0.55   # share of the budget for lift search before splicing starts
_BIG = 10 ** 9
_TABLE_CACHE = {}
_TABLE_CACHE_CAP = 12  # tables are N x N, so keep the cache small


# ----------------------------------------------------------------------------
# Baseline: projective plane incidence graph (exact for D = 3, d - 1 a prime power).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k with a bounded annealed connection set.
#
# Vertices A_x and B_y (x, y in G). Edge A_x -- B_{x s} for s in S, |S| = d.
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
# Multi-base voltage lifts over semidirect products, annealed.
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# NEW: pair splicing + switch annealing.
#
# Grow a valid graph by two vertices p (side A) and q (side B) while keeping
# every old vertex's degree. Take d edges (a_i, b_i) with distinct a_i and
# distinct b_i, and rewire each to (p, b_i) and (a_i, q). Then p and q have
# degree d, and the graph is bipartite with n + 2 vertices. Diameter is then
# repaired by degree-preserving bipartite 2-switches
#     (a,b),(c,e)  ->  (a,e),(c,b)
# that minimise the number of vertex pairs farther than D apart.
# ----------------------------------------------------------------------------

def _cost_sets(n, nb, D):
    """Number of unordered vertex pairs at distance > D, from neighbour sets nb."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _switch_anneal(n, E, D, rng, deadline, iters):
    """Anneal bipartite 2-switches on edge list E (each entry [a, b], a in side 0).

    Returns True if the graph reaches diameter <= D. E is updated in place.
    """
    nb = [set() for _ in range(n)]
    for a, b in E:
        nb[a].add(b)
        nb[b].add(a)
    cost = _cost_sets(n, nb, D)
    m = len(E)
    for it in range(iters):
        if cost == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in nb[a] or b in nb[c]:
            continue
        nb[a].discard(b); nb[b].discard(a); nb[c].discard(e); nb[e].discard(c)
        nb[a].add(e); nb[e].add(a); nb[c].add(b); nb[b].add(c)
        new = _cost_sets(n, nb, D)
        temp = 0.05 + 1.0 * (1.0 - it / iters)
        if new <= cost or rng.random() < math.exp(-(new - cost) / temp):
            E[i] = [a, e]
            E[j] = [c, b]
            cost = new
        else:
            nb[a].discard(e); nb[e].discard(a); nb[c].discard(b); nb[b].discard(c)
            nb[a].add(b); nb[b].add(a); nb[c].add(e); nb[e].add(c)
    return cost == 0


def _splice_grow(n, edges, d, D, deadline, rng):
    """Repeatedly add a vertex pair by splicing, then repair diameter by switch annealing."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)
    cur_E = [[u, v] if color[u] == 0 else [v, u] for u, v in edges]
    cur_n = n

    while time.monotonic() < deadline:
        p, q = cur_n, cur_n + 1
        E2 = [list(x) for x in cur_E]
        idxs = list(range(len(E2)))
        rng.shuffle(idxs)
        used_a, used_b, picks = set(), set(), []
        for i in idxs:
            a, b = E2[i]
            if a in used_a or b in used_b:
                continue
            used_a.add(a)
            used_b.add(b)
            picks.append(i)
            if len(picks) == d:
                break
        if len(picks) < d:
            break
        for i in picks:
            a, b = E2[i]
            E2[i] = [p, b]          # p (side A) joins old side-B vertex b
            E2.append([a, q])       # old side-A vertex a joins q (side B)
        if _switch_anneal(cur_n + 2, E2, D, rng, deadline, SPLICE_ITERS):
            cur_n += 2
            cur_E = E2

    return cur_n, [(u, v) for u, v in cur_E]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    main_deadline = start + MAIN_FRACTION * budget
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

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Lift search: bi-Cayley lifts mixed with multi-base lifts.
    bicayley_prob = 0.7 if D >= 4 else 0.5
    sweep = None
    while best[0] < moore and time.monotonic() < main_deadline:
        n_best = best[0]

        if d >= 2 and rng.random() < bicayley_prob:
            lo = n_best // 2 + 1
            if lo > moore // 2:
                break
            if sweep is None or sweep < lo or sweep > lo + SWEEP_WINDOW:
                sweep = lo
            N = sweep
            sweep += 1
            found = _bicayley_search(N, d, D, rng, main_deadline)
            if found is not None:
                T, S = found
                consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
        else:
            k = rng.choice((2, 3))
            lo = n_best // (2 * k) + 1
            if 2 * k * lo > moore:
                continue
            G = lo + rng.randrange(max(2, lo // 10))
            m, k2, r = rng.choice(_groups(G))
            order, mul, _ = lib.semidirect_group(m, k2, r)
            res = _anneal(d, D, k, order, mul, rng, main_deadline, ANNEAL_ITERS)
            if res is not None:
                consider(res[0], res[1])

    # Splice phase: grow the best valid graph by vertex pairs with the remaining time.
    if best[0] < moore and D >= 3 and time.monotonic() < deadline:
        n2, e2 = _splice_grow(best[0], best[1], d, D, deadline, rng)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
