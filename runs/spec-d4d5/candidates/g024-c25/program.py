import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Shared helpers
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs count)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _orient(n, edges):
    """Return edges as (left, right) pairs using a 2-colouring of the bipartite graph."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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
    return [(u, v) if color[u] == 0 else (v, u) for u, v in edges]


def _regular_oriented(n, edges, d):
    """Oriented (left, right) edge list if the graph is d-regular, else None."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    if any(x != d for x in deg):
        return None
    return _orient(n, edges)


# ----------------------------------------------------------------------------
# Family A: edge-swap annealing with vertex-insertion growth (new, unsymmetric).
#
# The state is a d-regular bipartite graph stored as oriented edges E = [(l, r)].
# Moves: 2-switch (l1,r1),(l2,r2) -> (l1,r2),(l2,r1), which keeps all degrees.
# When the diameter is satisfied, we insert two vertices x (left) and y (right):
# d edges (l_k, r_k) with distinct endpoints become (x, r_k) and (l_k, y). This keeps
# every degree at d, so the search continues from a valid graph of order n+2.
# ----------------------------------------------------------------------------

def _apply(E, adj, eset, i, j, new1, new2):
    """Replace E[i], E[j] by new1, new2 and keep adjacency lists and edge set in sync."""
    for u, v in (E[i], E[j]):
        adj[u].remove(v)
        adj[v].remove(u)
        eset.discard((u, v))
    E[i] = new1
    E[j] = new2
    for u, v in (new1, new2):
        adj[u].append(v)
        adj[v].append(u)
        eset.add((u, v))


def _grow(n, E, adj, eset, d, rng):
    """Insert a left vertex x and a right vertex y, keeping all degrees. Returns new n, or -1."""
    idx = list(range(len(E)))
    rng.shuffle(idx)
    chosen, usedL, usedR = [], set(), set()
    for i in idx:
        l, r = E[i]
        if l in usedL or r in usedR:
            continue
        chosen.append(i)
        usedL.add(l)
        usedR.add(r)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return -1
    x, y = n, n + 1
    adj.append([])
    adj.append([])
    for i in chosen:
        l, r = E[i]
        adj[l].remove(r)
        adj[r].remove(l)
        eset.discard((l, r))
        E[i] = (x, r)
        adj[x].append(r)
        adj[r].append(x)
        eset.add((x, r))
        E.append((l, y))
        adj[l].append(y)
        adj[y].append(l)
        eset.add((l, y))
    return n + 2


def _swap_search(n, E, d, D, best, deadline, rng):
    """Anneal 2-switches to reach diameter <= D; grow by 2 vertices each time it succeeds.

    `best` is a mutable [n, edges] holder that is updated only with validated graphs.
    """
    adj = [[] for _ in range(n)]
    eset = set()
    for l, r in E:
        adj[l].append(r)
        adj[r].append(l)
        eset.add((l, r))
    cost = _bad(n, adj, D)
    t = 0
    while True:
        if cost == 0:
            if n > best[0]:
                edges = [(int(l), int(r)) for l, r in E]
                if lib.is_valid(n, edges, d, D):
                    best[0], best[1] = n, edges
            if time.monotonic() >= deadline:
                break
            n2 = _grow(n, E, adj, eset, d, rng)
            if n2 < 0:
                break
            n = n2
            cost = _bad(n, adj, D)
            t = 0
            continue
        if time.monotonic() >= deadline:
            break
        t += 1
        L = len(E)
        i = rng.randrange(L)
        j = rng.randrange(L)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or (a, e) in eset or (c, b) in eset:
            continue
        old1, old2 = E[i], E[j]
        _apply(E, adj, eset, i, j, (a, e), (c, b))
        c2 = _bad(n, adj, D)
        delta = c2 - cost
        T = 0.4 + 3.0 * math.exp(-t / 800.0)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _apply(E, adj, eset, i, j, old1, old2)


# ----------------------------------------------------------------------------
# Family B: annealed voltage lifts over Z_m x| Z_k (floor from the parent approach).
# Vertices A_{i,g} = i*G + g (left) and B_{j,h} = (k+j)*G + h (right).
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for every g.
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
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    return _bad(N, adj, D)


def _lift_anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])

    def perm(s):
        return [mul(g, s) for g in range(G)]

    perms = [perm(s) for _, _, s in darts]
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
            perms[idx] = perm(new_s)
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
        E = set()
        for (i, j, _s), pm in zip(darts, perms):
            for g in range(G):
                E.add((i * G + g, (k + j) * G + pm[g]))
        return 2 * k * G, sorted(E)
    return None


def _lift_phase(d, D, best, deadline, rng):
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 2, 2, 3, 4])
        base = best[0] // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, 3))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _lift_anneal(d, D, k, order, mul, rng, deadline, 1500)
        if res is not None:
            n, edges = res
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best[0], best[1] = n, edges


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, 0.72 * time_limit - 0.5)
    end = start + budget
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    kd_edges = [(i, d + j) for i in range(d) for j in range(d)]
    best = [2 * d, kd_edges]

    # Bipartite Moore bound for max degree d and diameter D.
    mb = 2 * sum((d - 1) ** i for i in range(D))
    if best[0] >= mb or D == 2:
        return best[0], best[1]

    # Projective plane incidence graph meets the bound when d - 1 is a prime power (D = 3).
    if D >= 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = [n, e]
    if best[0] >= mb:
        return best[0], best[1]

    try:
        if D >= 4:
            _lift_phase(d, D, best, start + 0.35 * budget, rng)
        E = _regular_oriented(best[0], best[1], d)
        if E is not None:
            _swap_search(best[0], E, d, D, best, end, rng)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2 * d, kd_edges
    return best[0], best[1]
