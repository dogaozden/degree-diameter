import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Algebraic bases: projective plane incidence and Araujo-Pardo & Lopez graph.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph for degree d when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k, annealed.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# ----------------------------------------------------------------------------

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
    """Permutation g -> mul(g, s) of the group."""
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
# NEW: switch-based vertex growth.
#
# Starting from a valid bipartite graph, add one A-vertex and one B-vertex
# (both of degree 0), then run simulated annealing on the bipartite graph.
# Moves are:
#   * add an edge between a deficient A-vertex and a deficient B-vertex;
#   * 2-switch: replace (a1,b1),(a2,b2) by (a1,b2),(a2,b1), which keeps every
#     degree fixed and keeps the graph bipartite.
# Cost = (#pairs at distance > D) + 0.3 * (total degree deficit).
# Success means zero bad pairs, and the state is then a valid graph of order n+2.
# ----------------------------------------------------------------------------

def _colour(n, adj):
    """Two-colouring of a bipartite graph given as adjacency sets."""
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


def _bad_adj(n, adj, D):
    """Number of unordered pairs at distance > D, from adjacency sets, via bitmask balls."""
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


def _rewire(adj, el, i, j, ni, nj):
    """Replace edges el[i], el[j] by ni, nj, updating adjacency sets in place."""
    for a, b in (el[i], el[j]):
        adj[a].discard(b)
        adj[b].discard(a)
    for a, b in (ni, nj):
        adj[a].add(b)
        adj[b].add(a)
    el[i] = ni
    el[j] = nj


def _sa_fill(n, color, adj, el, d, D, deadline, rng, iters):
    """Anneal the current graph (n vertices) until all pairs are within distance D."""
    A = [v for v in range(n) if color[v] == 0]
    B = [v for v in range(n) if color[v] == 1]

    def score():
        bad = _bad_adj(n, adj, D)
        deficit = sum(d - len(adj[v]) for v in range(n))
        return bad + 0.3 * deficit, bad

    cur, bad = score()
    for it in range(iters):
        if bad == 0:
            return True
        if (it & 15) == 0 and time.monotonic() > deadline:
            return False
        T = 1.0 * (0.05 ** (it / iters))

        if rng.random() < 0.25:
            added = False
            for _ in range(40):
                a = rng.choice(A)
                b = rng.choice(B)
                if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
                    adj[a].add(b)
                    adj[b].add(a)
                    el.append((a, b))
                    added = True
                    break
            if added:
                cur, bad = score()
            continue

        if len(el) < 2:
            continue
        i = rng.randrange(len(el))
        j = rng.randrange(len(el))
        if i == j:
            continue
        a1, b1 = el[i]
        a2, b2 = el[j]
        if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue
        old_i, old_j = el[i], el[j]
        _rewire(adj, el, i, j, (a1, b2), (a2, b1))
        c2, bad2 = score()
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur, bad = c2, bad2
        else:
            _rewire(adj, el, i, j, old_i, old_j)
    return bad == 0


def _switch_grow(n, edges, d, D, deadline, rng, iters):
    """Repeatedly add two vertices (one per side) and repair with switch annealing."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _colour(n, adj)
    el = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    best = (n, list(edges))
    while time.monotonic() < deadline:
        n2 = n + 2
        adj.append(set())
        adj.append(set())
        color.append(0)
        color.append(1)
        if not _sa_fill(n2, color, adj, el, d, D, deadline, rng, iters):
            break
        n = n2
        best = (n, [(a, b) for a, b in el])
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.8 * time_limit
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
            ap = _araujo(d)
            if ap is not None:
                consider(ap[0], ap[1])

            # Voltage-lift search over semidirect products (the main source of records).
            lift_end = start + 0.6 * total
            if D >= 5:
                ks = [1, 1, 2, 2, 3, 4]
                anneal_iters = 1500
            else:
                ks = [1, 1, 2, 3]
                anneal_iters = 400
            while time.monotonic() < lift_end:
                k = rng.choice(ks)
                base = best_n // (2 * k)
                if D >= 5:
                    G = max(2, base + 1 + rng.randrange(0, 3))
                else:
                    G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
                g = _sample_group(G, rng)
                if g is None:
                    continue
                order, mul = g
                res = _anneal(d, D, k, order, mul, rng, lift_end, iters=anneal_iters)
                if res is not None:
                    consider(res[0], res[1])

            # Switch-annealed growth from the best valid graph found so far.
            if time.monotonic() < deadline:
                gn, ge = _switch_grow(best_n, best[1], d, D, deadline, rng, 3000)
                consider(gn, ge)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
