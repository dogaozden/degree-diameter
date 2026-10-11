import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Phase 0: cheap algebraic starting points (instant, always valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph when q = d - 2 is a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Phase 1: annealed bi-Cayley voltage lifts over semidirect products.
# Gives a large valid seed graph for phase 2 to grow from.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (order, mul), or None."""
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
    """Number of (representative, vertex) pairs not reached within D. Zero means valid."""
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


def _edges_lift(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and B-assignments of a bi-Cayley lift."""
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
        return _edges_lift(k, G, darts, perms)
    return None


def _phase1(d, D, best, deadline, rng):
    """Repeatedly anneal voltage lifts whose order is above the current best."""
    moore = lib.moore_bound(d, D)
    ks = [1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    iters = 1500 if D >= 5 else 400
    while time.monotonic() < deadline and best[0] < moore:
        k = rng.choice(ks)
        base = best[0] // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, 3))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal_lift(d, D, k, order, mul, rng, deadline, iters)
        if res is not None and res[0] > best[0]:
            n, e = res
            if lib.is_valid(n, e, d, D):
                best = (n, e)
    return best


# ----------------------------------------------------------------------------
# Phase 2 (new, high-risk): grow-and-repair by simulated annealing on the
# raw bipartite graph. Each step inserts one vertex per side, wired in by
# subdividing existing edges (degrees of old vertices are preserved), then
# edge moves minimize the number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _bad_pairs(n, adj, D):
    """Unordered pairs at distance > D (unreachable counts), via bitmask balls."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _sides(n, adj):
    side = [-1] * n
    for s in range(n):
        if side[s] != -1:
            continue
        side[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if side[v] == -1:
                    side[v] = 1 - side[u]
                    stack.append(v)
    return side


def _find(n, rng, ok, tries=40):
    for _ in range(tries):
        z = rng.randrange(n)
        if ok(z):
            return z
    return None


def _insert_pair(n, adj, side, d, rng):
    """Add vertices a (side 0) and b (side 1) by subdividing edges x-y into x-b and a-y.

    Every old vertex keeps its degree; a and b receive up to d neighbours each.
    """
    a, b = n, n + 1
    adj.append(set())
    adj.append(set())
    side.append(0)
    side.append(1)
    for _ in range(d):
        for _try in range(200):
            x = rng.randrange(n)
            if side[x] != 0 or not adj[x]:
                continue
            y = rng.choice(tuple(adj[x]))
            if y in adj[a] or x in adj[b]:
                continue
            adj[x].discard(y)
            adj[y].discard(x)
            adj[a].add(y)
            adj[y].add(a)
            adj[b].add(x)
            adj[x].add(b)
            break


def _phase2(d, D, n, edges, best, deadline, rng):
    moore = lib.moore_bound(d, D)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    side = _sides(n, adj)
    cur = _bad_pairs(n, adj, D)
    it = 0

    while time.monotonic() < deadline:
        if cur == 0:
            if n > best[0]:
                snap = (n, [(u, v) for u in range(n) for v in adj[u] if u < v])
                if lib.is_valid(snap[0], snap[1], d, D):
                    best = snap
            if n + 2 > moore:
                break
            _insert_pair(n, adj, side, d, rng)
            n += 2
            cur = _bad_pairs(n, adj, D)
            continue

        it += 1
        T = 2.0 * (0.1 ** ((it % 3000) / 3000.0))
        r = rng.random()

        if r < 0.1:
            # Add a missing edge between two deficient opposite-side vertices.
            x = _find(n, rng, lambda t: len(adj[t]) < d)
            if x is None:
                continue
            z = _find(n, rng, lambda t: side[t] != side[x] and len(adj[t]) < d and t not in adj[x])
            if z is None:
                continue
            adj[x].add(z)
            adj[z].add(x)
            cur = _bad_pairs(n, adj, D)

        elif r < 0.55:
            # Rewire one endpoint of an edge to a vertex with spare degree.
            x = rng.randrange(n)
            if not adj[x]:
                continue
            y = rng.choice(tuple(adj[x]))
            z = _find(n, rng, lambda t: side[t] != side[x] and len(adj[t]) < d
                      and t not in adj[x] and t != y)
            if z is None:
                continue
            adj[x].discard(y)
            adj[y].discard(x)
            adj[x].add(z)
            adj[z].add(x)
            new = _bad_pairs(n, adj, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                adj[x].discard(z)
                adj[z].discard(x)
                adj[x].add(y)
                adj[y].add(x)

        else:
            # Degree-preserving double edge swap on two same-side vertices.
            x1 = rng.randrange(n)
            x2 = rng.randrange(n)
            if x1 == x2 or side[x1] != side[x2] or not adj[x1] or not adj[x2]:
                continue
            y1 = rng.choice(tuple(adj[x1]))
            y2 = rng.choice(tuple(adj[x2]))
            if y1 == y2 or y2 in adj[x1] or y1 in adj[x2]:
                continue
            adj[x1].discard(y1)
            adj[y1].discard(x1)
            adj[x2].discard(y2)
            adj[y2].discard(x2)
            adj[x1].add(y2)
            adj[y2].add(x1)
            adj[x2].add(y1)
            adj[y1].add(x2)
            new = _bad_pairs(n, adj, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                adj[x1].discard(y2)
                adj[y2].discard(x1)
                adj[x2].discard(y1)
                adj[y1].discard(x2)
                adj[x1].add(y1)
                adj[y1].add(x1)
                adj[x2].add(y2)
                adj[y2].add(x2)

    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        for make in (_araujo, _best_pg):
            try:
                c = make(d)
                if c is not None and c[0] > best[0] and lib.is_valid(c[0], c[1], d, D):
                    best = (c[0], list(c[1]))
            except Exception:
                pass

    if best[0] < lib.moore_bound(d, D):
        try:
            best = _phase1(d, D, best, t0 + 0.4 * time_limit, rng)
        except Exception:
            pass
        try:
            best = _phase2(d, D, best[0], list(best[1]), best,
                           t0 + 0.85 * time_limit, rng)
        except Exception:
            pass

    try:
        ok = lib.is_valid(best[0], best[1], d, D)
    except Exception:
        ok = False
    if not ok:
        best = lib.haar_graph(d, range(d))
    return best
