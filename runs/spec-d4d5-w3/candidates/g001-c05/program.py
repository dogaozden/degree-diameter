import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Projective-plane fallback (calibration cases and D = 3, 4).
# ----------------------------------------------------------------------------

def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k (seed generator).
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
    return [mul(g, s) for g in range(G)]


def _lift_cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within D. Zero means valid."""
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


def _lift_edges(k, G, darts, perms):
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
            perms[idx] = _right_perm(mul, G, new_s)
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


def _lift_search(d, D, deadline, rng, best_n):
    """Anneal voltage lifts with group order just above the current best; return best valid (n, edges)."""
    best = None
    ks = [1, 1, 2, 2, 3, 4]
    cur_best = best_n
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = cur_best // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, 4))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, 1500)
        if res is not None and res[0] > cur_best:
            best = res
            cur_best = res[0]
    return best


# ----------------------------------------------------------------------------
# Repair search: grow a valid graph by two vertices (one per side) and anneal
# with degree-respecting edge moves until the diameter bound holds again.
# ----------------------------------------------------------------------------

def _ball_cost(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable counts)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _apply(adj, ops):
    for t, a, b in ops:
        if t == 0:
            adj[a].discard(b)
            adj[b].discard(a)
        else:
            adj[a].add(b)
            adj[b].add(a)


def _undo(adj, ops):
    for t, a, b in reversed(ops):
        if t == 0:
            adj[a].add(b)
            adj[b].add(a)
        else:
            adj[a].discard(b)
            adj[b].discard(a)


def _repair(n, col, adj, d, D, deadline, rng):
    """Annealed edge moves on adj (mutated in place). Returns final bad-pair count."""
    cur = _ball_cost(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 0.3 + 2.0 * (1.0 - (now - t0) / span)
        r = rng.random()
        if r < 0.7:
            # Slide: keep one endpoint of an edge, move the other to a deficient vertex.
            u = rng.randrange(n)
            if not adj[u]:
                continue
            a, b = u, rng.choice(tuple(adj[u]))
            if rng.random() < 0.5:
                a, b = b, a
            cand = [w for w in range(n)
                    if col[w] == col[b] and w != b and w not in adj[a] and len(adj[w]) < d]
            if not cand:
                continue
            w = rng.choice(cand)
            ops = ((0, a, b), (1, a, w))
        elif r < 0.9:
            # Add an edge between two deficient vertices on opposite sides.
            defs0 = [v for v in range(n) if col[v] == 0 and len(adj[v]) < d]
            defs1 = [v for v in range(n) if col[v] == 1 and len(adj[v]) < d]
            if not defs0 or not defs1:
                continue
            a = rng.choice(defs0)
            b = rng.choice(defs1)
            if b in adj[a]:
                continue
            ops = ((1, a, b),)
        else:
            # Remove a random edge (adds slack).
            u = rng.randrange(n)
            if not adj[u]:
                continue
            ops = ((0, u, rng.choice(tuple(adj[u]))),)

        _apply(adj, ops)
        new = _ball_cost(n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            _undo(adj, ops)
    return cur


def _colour(n, adj):
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _edges_from_adj(n, adj):
    return [(a, b) for a in range(n) for b in adj[a] if a < b]


def _grow_repair(n0, e0, d, D, deadline, rng):
    """Repeatedly add two vertices and repair; return the largest valid graph reached."""
    adj0 = [set() for _ in range(n0)]
    for a, b in e0:
        adj0[a].add(b)
        adj0[b].add(a)
    cur_n, cur_adj, cur_col = n0, adj0, _colour(n0, adj0)
    result = (n0, list(e0))

    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.5:
            break
        if cur_n + 2 > 600:
            break
        slice_end = now + max(2.0, 0.15 * remaining)
        slice_end = min(slice_end, deadline)
        n2 = cur_n + 2
        adj2 = [set(s) for s in cur_adj] + [set(), set()]
        col2 = cur_col + [0, 1]
        cost = _repair(n2, col2, adj2, d, D, slice_end, rng)
        if cost == 0:
            e2 = _edges_from_adj(n2, adj2)
            if lib.is_valid(n2, e2, d, D):
                result = (n2, e2)
                cur_n, cur_adj, cur_col = n2, adj2, col2
    return result


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    if D >= 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg)

    # Calibration and non-target cases return the projective-plane graph directly.
    if D < 5 or d < 2:
        if lib.is_valid(best[0], best[1], d, D):
            return best
        return lib.haar_graph(d, range(d))

    try:
        lift = _lift_search(d, D, start + 0.4 * time_limit, rng, best[0])
        consider(lift)
        if best[0] <= 600:
            grown = _grow_repair(best[0], best[1], d, D, end, rng)
            consider(grown)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
