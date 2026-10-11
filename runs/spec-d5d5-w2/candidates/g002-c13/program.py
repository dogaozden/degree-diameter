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
SPLIT_D5 = 0.5         # fraction of budget spent on lift search before repair growth
REPAIR_SLICE_FRAC = 0.3  # fraction of remaining time given to each repair attempt
REPAIR_MIN_SLICE = 2.0   # seconds, minimum per repair attempt
_BIG = 10 ** 9
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# D = 3 baseline: projective plane incidence graph.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k with a bounded annealed connection set.
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
    if len(_TABLE_CACHE) >= 48:
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
# Bold change: vertex insertion into a valid graph, then annealed edge-switch
# repair. Each step adds one A-vertex and one B-vertex by re-routing a matching
# of d existing edges through them (degrees are preserved). Degree-preserving
# bipartite switches then drive the number of bad pairs to zero.
# ----------------------------------------------------------------------------

def _sides(n, edges):
    """2-colour the graph (assumed bipartite); return list of 0/1 side labels."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    side = [-1] * n
    for s in range(n):
        if side[s] != -1:
            continue
        side[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if side[w] == -1:
                    side[w] = 1 - side[u]
                    stack.append(w)
    return side


def _state(n, oriented):
    """Adjacency lists, edge set and edge list for oriented (A, B) edges."""
    adj = [[] for _ in range(n)]
    eset = set()
    E = []
    for a, b in oriented:
        adj[a].append(b)
        adj[b].append(a)
        eset.add((a, b))
        E.append((a, b))
    return adj, eset, E


def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (unreachable counts)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _replace(adj, eset, E, i, na, nb):
    """Replace edge number i by (na, nb), updating adjacency and edge set."""
    oa, ob = E[i]
    adj[oa].remove(ob)
    adj[ob].remove(oa)
    eset.discard((oa, ob))
    adj[na].append(nb)
    adj[nb].append(na)
    eset.add((na, nb))
    E[i] = (na, nb)


def _insert_pair(n, oriented, d, rng):
    """Add A-vertex n and B-vertex n+1, re-routing d matched edges through them."""
    idx = list(range(len(oriented)))
    rng.shuffle(idx)
    used_a = set()
    used_b = set()
    chosen = []
    for i in idx:
        a, b = oriented[i]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        chosen.append(i)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    A_new, B_new = n, n + 1
    chosen_set = set(chosen)
    new_edges = [e for i, e in enumerate(oriented) if i not in chosen_set]
    for i in chosen:
        a, b = oriented[i]
        new_edges.append((A_new, b))
        new_edges.append((a, B_new))
    return n + 2, new_edges


def _anneal_repair(n, adj, E, eset, d, D, rng, t0, t_end):
    """Degree-preserving bipartite edge switches minimising bad pairs. Returns final cost."""
    cur = _bad_pairs(n, adj, D)
    m = len(E)
    span = max(1e-6, t_end - t0)
    frac = 0.0
    it = 0
    while cur > 0 and m >= 2:
        it += 1
        if (it & 7) == 0:
            now = time.monotonic()
            if now >= t_end:
                break
            frac = (now - t0) / span
        temp = max(0.05, 1.5 * (1.0 - frac))
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
        _replace(adj, eset, E, i, a1, b2)
        _replace(adj, eset, E, j, a2, b1)
        new = _bad_pairs(n, adj, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
        else:
            _replace(adj, eset, E, j, a2, b2)
            _replace(adj, eset, E, i, a1, b1)
    return cur


def _repair_growth(best, d, D, rng, deadline, moore):
    """Repeatedly insert a vertex pair and repair; return the largest valid graph found."""
    n, edges = best
    side = _sides(n, edges)
    cur_n = n
    cur = [(u, v) if side[u] == 0 else (v, u) for u, v in edges]
    result = best
    while time.monotonic() < deadline:
        if cur_n + 2 > moore:
            break
        ins = _insert_pair(cur_n, cur, d, rng)
        if ins is None:
            break
        nn, ne = ins
        adj, eset, E = _state(nn, ne)
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.05:
            break
        slice_end = min(deadline, now + max(REPAIR_MIN_SLICE, REPAIR_SLICE_FRAC * remaining))
        cost = _anneal_repair(nn, adj, E, eset, d, D, rng, now, slice_end)
        if cost == 0:
            cand_edges = list(E)
            if lib.is_valid(nn, cand_edges, d, D):
                result = (nn, cand_edges)
                cur_n, cur = nn, cand_edges
    return result


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

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if best[0] >= moore:
            return best

    # Phase 1: lift search (bi-Cayley and multi-base annealing).
    use_repair = D >= 5 and d >= 3
    phase1 = start + (SPLIT_D5 if use_repair else 1.0) * budget

    sweep = None
    while best[0] < moore and time.monotonic() < phase1:
        n_best = best[0]

        if d >= 2 and rng.random() < 0.6:
            lo = n_best // 2 + 1
            if lo > moore // 2:
                break
            if sweep is None or sweep < lo or sweep > lo + SWEEP_WINDOW:
                sweep = lo
            N = sweep
            sweep += 1
            found = _bicayley_search(N, d, D, rng, phase1)
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
            res = _anneal(d, D, k, order, mul, rng, phase1, ANNEAL_ITERS)
            if res is not None:
                consider(res[0], res[1])

    # Phase 2 (bold): grow the best graph by vertex-pair insertion and repair.
    if use_repair and best[0] < moore and time.monotonic() < deadline:
        grown = _repair_growth(best, d, D, rng, deadline, moore)
        if grown is not None and grown[0] > best[0]:
            consider(grown[0], grown[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
