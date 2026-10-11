import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Bitset distance cost and graph helpers.
# ----------------------------------------------------------------------------

def _bad_pairs_adj(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs count)."""
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


def _adjacency(n, E):
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    return adj


def _two_colour(n, adj):
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


def _oriented(n, edges):
    """Orient each edge as (side-0 vertex, side-1 vertex) for a bipartite graph."""
    col = _two_colour(n, _adjacency(n, edges))
    return [(u, v) if col[u] == 0 else (v, u) for u, v in edges]


# ----------------------------------------------------------------------------
# Bold phase: add vertex pairs, then repair by degree-preserving edge switches.
# ----------------------------------------------------------------------------

def _add_pair(n, E, d, rng):
    """Insert a new side-0 vertex a and side-1 vertex b.

    Takes up to d edges (x, y) with distinct x and distinct y, replaces each by (x, b),
    and adds (a, y). Degrees of all old vertices are unchanged.
    """
    a, b = n, n + 1
    order = list(range(len(E)))
    rng.shuffle(order)
    used_x, used_y, chosen = set(), set(), []
    for idx in order:
        x, y = E[idx]
        if x in used_x or y in used_y:
            continue
        chosen.append(idx)
        used_x.add(x)
        used_y.add(y)
        if len(chosen) == d:
            break
    if not chosen:
        return None
    E2 = list(E)
    for idx in chosen:
        x, y = E2[idx]
        E2[idx] = (x, b)
        E2.append((a, y))
    return n + 2, E2


def _sa_repair(n, E, D, deadline, rng):
    """Anneal degree-preserving switches to drive the bad-pair count to zero."""
    E = list(E)
    eset = set(E)
    m = len(E)

    def cost():
        return _bad_pairs_adj(n, _adjacency(n, E), D)

    c = cost()
    if c == 0:
        return E, True
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while c > 0:
        now = time.monotonic()
        if now >= deadline or m < 2:
            break
        T = max(0.15, 1.5 * (1.0 - (now - t0) / span))
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
        eset.difference_update(((a1, b1), (a2, b2)))
        eset.update(((a1, b2), (a2, b1)))
        c2 = cost()
        delta = c2 - c
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            c = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            eset.difference_update(((a1, b2), (a2, b1)))
            eset.update(((a1, b1), (a2, b2)))
    return E, c == 0


def _bold(d, D, n, E, rng, deadline, consider):
    """Repeatedly add a vertex pair and repair it; keep every valid success."""
    cur_n, cur_E = n, E
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.2:
            break
        nxt = _add_pair(cur_n, cur_E, d, rng)
        if nxt is None:
            break
        tn, tE = nxt
        sol, ok = _sa_repair(tn, tE, D, now + min(remaining, 5.0), rng)
        if ok:
            edges = list(sol)
            if lib.is_valid(tn, edges, d, D):
                cur_n, cur_E = tn, edges
                consider(tn, edges)


# ----------------------------------------------------------------------------
# Lift phase: annealed group voltage lifts over Z_m x| Z_k.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
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


def _lift_cost(k, G, D, darts, perms):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
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


def _lift_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _lift_anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
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
            perms[idx] = [mul(g, new_s) for g in range(G)]
            c2 = _lift_cost(k, G, D, darts, perms)
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
            c2 = _lift_cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _lift_edges(k, G, darts, perms)
    return None


def _lift_phase(d, D, deadline, rng, best, consider):
    ks = [1, 1, 2, 2, 3, 4]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        best_n = best[0][0]
        G = max(2, best_n // (2 * k) + 1 + rng.randrange(0, 3))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _lift_anneal(d, D, k, order, mul, rng, deadline, 1500)
        if res is not None:
            consider(res[0], res[1])


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]
        if lib.is_valid(n, cyc, d, D):
            return n, cyc

    # Safe fallback: K_{d,d} has diameter 2.
    best = [lib.haar_graph(d, range(d))]

    def consider(n, e):
        if n > best[0][0] and lib.is_valid(n, e, d, D):
            best[0] = (n, e)

    if D >= 3:
        q = next((q for q in range(min(d - 1, 16), 1, -1) if lib.is_prime_power(q)), None)
        if q is not None:
            consider(*lib.projective_plane_incidence(q))

    if D < 4:
        return best[0]

    try:
        if D >= 5:
            _lift_phase(d, D, start + 0.4 * time_limit, rng, best, consider)
        n0, e0 = best[0]
        E0 = _oriented(n0, e0)
        _bold(d, D, n0, E0, rng, start + 0.9 * time_limit, consider)
    except Exception:
        pass

    return best[0]
