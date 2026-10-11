import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2 (annealed).
# Used to produce the seed graph for the repair search when D >= 5.
# ----------------------------------------------------------------------------

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


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return 10 ** 9
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

    T0 = max(1.0, 0.05 * cost) if cost < 10 ** 9 else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

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
            if delta <= 0 or rng.random() < math.exp(-delta / T):
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
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# NEW: unstructured repair search (grow-and-anneal on edge switches).
#
# State: a bipartite graph with side 0 and side 1, max degree d, stored as
# adjacency sets plus an oriented edge list E of pairs [a, b] with a on side 0.
# Moves:
#   * grow:   add one vertex on each side, remove d-1 edges (a_i, b_i) with
#             distinct ends, and reconnect them as (x, b_i), (a_i, y), plus (x, y).
#             Degrees stay <= d and every old vertex keeps its degree.
#   * switch: replace (a, b), (c, e) by (a, e), (c, b). Degree-preserving and
#             bipartite-preserving.
# Cost = number of unordered pairs at distance > D. Anneal until cost is zero,
# then grow again. Every zero-cost state is a valid graph of that order.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs count)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _to_state(n, edges):
    adjl = [[] for _ in range(n)]
    for u, v in edges:
        adjl[u].append(v)
        adjl[v].append(u)
    side = _bipartition(n, adjl)
    adj = [set() for _ in range(n)]
    E = []
    for u, v in edges:
        a, b = (u, v) if side[u] == 0 else (v, u)
        E.append([a, b])
        adj[a].add(b)
        adj[b].add(a)
    return adj, E, side


def _saturate_state(adj, E, side, d, rng):
    """Greedily add edges between deficient opposite-side vertices (never breaks validity)."""
    n = len(adj)
    A = [v for v in range(n) if side[v] == 0 and len(adj[v]) < d]
    B = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]
    rng.shuffle(A)
    rng.shuffle(B)
    for a in A:
        for b in B:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) < d and b not in adj[a]:
                adj[a].add(b)
                adj[b].add(a)
                E.append([a, b])


def _grow_state(n, adj, E, side, d, rng):
    """Add one vertex per side with all degrees kept <= d. Returns new n, or None."""
    need = d - 1
    if need < 1:
        return None
    idxs = list(range(len(E)))
    rng.shuffle(idxs)
    chosen = []
    used_a, used_b = set(), set()
    for i in idxs:
        a, b = E[i]
        if a in used_a or b in used_b:
            continue
        chosen.append(i)
        used_a.add(a)
        used_b.add(b)
        if len(chosen) == need:
            break
    if len(chosen) < need:
        return None
    x, y = n, n + 1
    side.append(0)
    side.append(1)
    adj.append(set())
    adj.append(set())
    for i in chosen:
        a, b = E[i]
        adj[a].discard(b)
        adj[b].discard(a)
        E[i] = [x, b]
        adj[x].add(b)
        adj[b].add(x)
        E.append([a, y])
        adj[a].add(y)
        adj[y].add(a)
    E.append([x, y])
    adj[x].add(y)
    adj[y].add(x)
    return n + 2


def _apply_switch(adj, E, i, j, a, b, c, e):
    adj[a].discard(b)
    adj[b].discard(a)
    adj[c].discard(e)
    adj[e].discard(c)
    adj[a].add(e)
    adj[e].add(a)
    adj[c].add(b)
    adj[b].add(c)
    E[i] = [a, e]
    E[j] = [c, b]


def _undo_switch(adj, E, i, j, a, b, c, e):
    adj[a].discard(e)
    adj[e].discard(a)
    adj[c].discard(b)
    adj[b].discard(c)
    adj[a].add(b)
    adj[b].add(a)
    adj[c].add(e)
    adj[e].add(c)
    E[i] = [a, b]
    E[j] = [c, e]


def _repair(n, edges, d, D, deadline, rng, stall_limit=4000, temp=0.8):
    """Grow-and-anneal from a valid graph. Returns the largest valid (n, edges) found, or None."""
    adj, E, side = _to_state(n, edges)
    _saturate_state(adj, E, side, d, rng)
    cur_n = n
    best = None
    cur = _bad(cur_n, adj, D)
    min_cost = cur
    stall = 0
    while time.monotonic() < deadline:
        if cur == 0:
            best = (cur_n, [(a, b) for a, b in E])
            nn = _grow_state(cur_n, adj, E, side, d, rng)
            if nn is None:
                break
            cur_n = nn
            cur = _bad(cur_n, adj, D)
            min_cost = cur
            stall = 0
            continue
        if stall > stall_limit or len(E) < 2:
            break
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        _apply_switch(adj, E, i, j, a, b, c, e)
        new = _bad(cur_n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = new
            if cur < min_cost:
                min_cost = cur
                stall = 0
            else:
                stall += 1
        else:
            _undo_switch(adj, E, i, j, a, b, c, e)
            stall += 1
    return best


# ----------------------------------------------------------------------------
# Haar graph hill-climb (small D, secondary family).
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total_deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 5:
        # Phase 1: annealed group voltage lifts give a strong, structured seed.
        ks = [1, 1, 2, 2, 3, 4]
        lift_deadline = start + 0.35 * time_limit
        while time.monotonic() < lift_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, 3))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, lift_deadline, iters=1500)
            if res is not None:
                consider(res[0], res[1])

        # Phase 2: unstructured grow-and-repair from the best seed, with restarts.
        while time.monotonic() < total_deadline:
            run_rng = random.Random(rng.getrandbits(32))
            cand = _repair(best_n, best_e, d, D, total_deadline, run_rng)
            if cand is not None:
                consider(cand[0], cand[1])
    elif D == 4:
        # Small-D secondary family: Haar graphs by hill climbing.
        haar_m, haar_miss = d + 1, 0
        while haar_miss < 4 and time.monotonic() < total_deadline:
            S = _search_haar(d, D, haar_m, rng, total_deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, list(best_e)
