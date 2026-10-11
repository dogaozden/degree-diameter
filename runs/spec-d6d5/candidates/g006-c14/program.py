import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane base (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph utilities.
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


def _reach(n, adj, D):
    """Bitmask per vertex of all vertices within distance D (works with lists or sets)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt[v] = r
        reach = nxt
    return reach


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance more than D. Zero means diameter <= D."""
    return sum(n - r.bit_count() for r in _reach(n, adj, D)) // 2


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (only adds edges)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _compact(n, edges, keep):
    """Relabel the kept vertices to 0..m-1 and keep only edges between them."""
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    E = [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]
    return len(new), E


# ----------------------------------------------------------------------------
# Repair by deletion: remove far-off vertices in batches until diameter <= D.
# ----------------------------------------------------------------------------

def _repair(n, edges, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline and cur_n > 0:
        adj = [[] for _ in range(cur_n)]
        for u, v in cur_e:
            adj[u].append(v)
            adj[v].append(u)
        reach = _reach(cur_n, adj, D)
        bad = [cur_n - r.bit_count() for r in reach]
        if not any(bad):
            return cur_n, cur_e
        bad_v = [v for v in range(cur_n) if bad[v] > 0]
        rng.shuffle(bad_v)
        bad_v.sort(key=lambda v: -bad[v])
        batch = max(1, len(bad_v) // 12)
        dead = set(bad_v[:batch])
        keep = [v not in dead for v in range(cur_n)]
        cur_n, cur_e = _compact(cur_n, cur_e, keep)
    return None


# ----------------------------------------------------------------------------
# NEW: degree-preserving edge-split growth + double-edge-swap annealing ladder.
#
# _grow_split adds one vertex x on side 0 and one vertex y on side 1. It takes d
# edges a_t-b_t with pairwise distinct endpoints and rewires them to x-b_t and
# a_t-y. Every old vertex keeps its degree, x and y reach degree d, and the graph
# stays bipartite. The diameter may break, so _anneal_swap restores it with
# double-edge swaps (a1-b1, a2-b2 -> a1-b2, a2-b1). Swaps also keep every degree
# and bipartiteness. The cost is the number of pairs at distance > D. A success
# becomes the new snapshot, and the ladder grows by 2 vertices at a time.
# ----------------------------------------------------------------------------

def _orient(n, edges):
    """Orient each edge as (side-0 vertex, side-1 vertex)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)
    return [(u, v) if color[u] == 0 else (v, u) for u, v in edges]


def _state(n, pairs):
    """Mutable state: E is a list of [a, b] (a side 0, b side 1), adj is a list of sets."""
    adj = [set() for _ in range(n)]
    E = []
    for a, b in pairs:
        E.append([a, b])
        adj[a].add(b)
        adj[b].add(a)
    return E, adj


def _grow_split(n, E, adj, d, rng):
    """Add a new side-0 vertex and a new side-1 vertex by splitting d random edges. Returns new n or None."""
    order = list(range(len(E)))
    rng.shuffle(order)
    used_a, used_b, picks = set(), set(), []
    for idx in order:
        a, b = E[idx]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        picks.append(idx)
        if len(picks) == d:
            break
    if len(picks) < d:
        return None
    x, y = n, n + 1
    adj.append(set())
    adj.append(set())
    for idx in picks:
        a, b = E[idx]
        adj[a].discard(b)
        adj[b].discard(a)
        adj[x].add(b)
        adj[b].add(x)
        adj[a].add(y)
        adj[y].add(a)
        E[idx] = [x, b]
        E.append([a, y])
    return n + 2


def _rewire(adj, E, i, j, p, q, r, s):
    """Remove edges p-q and r-s, add p-s and r-q (E[i] = [p, s], E[j] = [r, q])."""
    adj[p].discard(q)
    adj[q].discard(p)
    adj[r].discard(s)
    adj[s].discard(r)
    adj[p].add(s)
    adj[s].add(p)
    adj[r].add(q)
    adj[q].add(r)
    E[i] = [p, s]
    E[j] = [r, q]


def _anneal_swap(n, E, adj, D, rng, deadline, iters):
    """Double-edge-swap annealing on the bad-pair count. Returns (success, cost)."""
    cost = _bad(n, adj, D)
    if cost == 0:
        return True, 0
    m = len(E)
    for it in range(iters):
        if time.monotonic() > deadline:
            break
        T = max(0.05, 1.0 * (1.0 - it / iters))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if b2 in adj[a1] or b1 in adj[a2]:
            continue
        _rewire(adj, E, i, j, a1, b1, a2, b2)
        c2 = _bad(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost == 0:
                return True, 0
        else:
            _rewire(adj, E, i, j, a1, b2, a2, b1)
    return cost == 0, cost


def _ladder(n, pairs, d, D, deadline, rng, consider):
    """Repeatedly grow by 2 vertices with degree-preserving splits, then anneal the diameter back to <= D."""
    fails = 0
    while time.monotonic() < deadline and fails < 6:
        E, adj = _state(n, pairs)
        new_n = _grow_split(n, E, adj, d, rng)
        if new_n is None:
            return
        ok, _ = _anneal_swap(new_n, E, adj, D, rng, deadline, 800)
        if ok:
            fails = 0
            n = new_n
            pairs = [(a, b) for a, b in E]
            consider(n, pairs)
        else:
            fails += 1


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
_REPAIR_MAX_COST = 60


def _sample_group(G, rng, k2_choices=None):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    choices = k2_choices or [1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    for _ in range(80):
        k2 = rng.choice(choices)
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


def _cost(k, G, D, darts, perms, limit=float("inf")):
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
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _perturb(darts, G, rng, flips):
    out = [list(x) for x in darts]
    for _ in range(flips):
        idx = rng.randrange(len(out))
        out[idx][2] = rng.randrange(G)
    return out


def _anneal(d, D, k, G, mul, rng, deadline, iters, start_darts=None, T0=1.0):
    """Simulated annealing over voltages and per-layer B-assignments.

    Returns (edges_or_None, darts, cost).
    """
    if start_darts is None:
        darts = _random_darts(d, k, G, rng)
    else:
        darts = [list(x) for x in start_darts]
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        u = 1.0 - rng.random()
        limit = cost - T * math.log(u)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms), darts, 0
    return None, darts, cost


def _lift_repair(d, D, k, G, mul, darts, deadline, rng):
    """Build the full lift from final darts, repair it, and saturate. Returns (n, edges) or None."""
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    N, E = _edges(k, G, darts, perms)
    rep = _repair(N, E, D, deadline, rng)
    if rep is None:
        return None
    n, e = rep
    e = _saturate_edges(n, e, d, rng)
    return n, e


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    group_deadline = start + 0.40 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if D == 2:
        return best_n, best_e

    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Calibration cases that already meet the Moore bound return immediately.
    if best_n >= lib._moore_bound(d, D):
        return best_n, best_e

    # Phase 1: annealed group voltage lifts with elite restarts and repair.
    ks = [1, 1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] if D >= 5 else None
    elite = {}
    while time.monotonic() < group_deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        lo = max(2, base + 1)
        if k == 1 and D >= 5:
            hi = lo + max(3, lo // 4)
        else:
            hi = lo + max(3, lo // 8)
        G = rng.randint(lo, hi)
        g = None
        if k2_pool is not None and rng.random() < 0.8:
            g = _sample_group(G, rng, k2_pool)
        if g is None:
            g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        key = (k, order)

        start_darts, T0, mul_use = None, 1.0, mul
        if key in elite and rng.random() < 0.5:
            _, st, mul_use = elite[key]
            start_darts = _perturb(st, order, rng, rng.randint(1, 3))
            T0 = 0.5

        iters = 1500 if k == 1 else 400
        res, darts_out, c = _anneal(d, D, k, order, mul_use, rng,
                                    group_deadline, iters, start_darts, T0)
        if res is not None:
            consider(res[0], res[1])
            continue

        if key not in elite or c < elite[key][0]:
            elite[key] = (c, darts_out, mul_use)

        if c <= _REPAIR_MAX_COST and rng.random() < 0.35 and time.monotonic() < group_deadline:
            rep_deadline = min(group_deadline, time.monotonic() + 4.0)
            out = _lift_repair(d, D, k, order, mul_use, darts_out, rep_deadline, rng)
            if out is not None:
                consider(out[0], out[1])

    # Phase 2: degree-preserving growth ladder with swap annealing.
    _ladder(best_n, _orient(best_n, best_e), d, D, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
