"""Deletion-from-larger-plane search for the D = 3 targets, with the parent's arc-extension,
group-lift annealing and K_{d,d} fallback kept as safe baselines.

Target construction (d >= 10, D = 3): take the incidence graph of PG(2, q) with q the smallest
prime power >= d, so every vertex has degree q+1 > d. Greedily delete vertices until the
induced subgraph has max degree <= d and diameter <= D, then re-add deleted vertices while
the property still holds. Every candidate is checked with lib.is_valid before use.
"""
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3, parent construction).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(lib.projective_points(q))}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_candidates(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# NEW: deletion from a larger projective plane, with greedy repair and re-adding.
# ----------------------------------------------------------------------------

def _pg_adj(q):
    """Incidence graph of PG(2, q) as (N, edges, adjacency lists)."""
    N, edges = lib.projective_plane_incidence(q)
    adj = [[] for _ in range(N)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return N, edges, adj


def _state(N, adj, alive, d, D):
    """Return (deg, bad, total_bad_pairs, total_excess) for the subgraph induced by alive.

    Paths may only use alive vertices (dead vertices have an empty reach set).
    """
    reach = [(1 << v) if alive[v] else 0 for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            if not alive[v]:
                continue
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    amask = 0
    for v in range(N):
        if alive[v]:
            amask |= 1 << v
    deg = [0] * N
    bad = [0] * N
    tb = 0
    ex = 0
    for v in range(N):
        if not alive[v]:
            continue
        deg[v] = sum(1 for u in adj[v] if alive[u])
        ex += max(0, deg[v] - d)
        b = (amask & ~reach[v]).bit_count()
        bad[v] = b
        tb += b
    return deg, bad, tb // 2, ex


def _greedy_delete(N, adj, d, D, rng, deadline):
    """Delete vertices (highest badness/excess first, random tie-break) until valid. None on timeout."""
    alive = [True] * N
    while True:
        if time.monotonic() > deadline:
            return None
        deg, bad, tb, ex = _state(N, adj, alive, d, D)
        if tb == 0 and ex == 0:
            return alive
        best_v, best_s = -1, -1e18
        for v in range(N):
            if not alive[v]:
                continue
            s = bad[v] + (3.0 if deg[v] > d else 0.0)
            s += 2.0 * sum(1 for u in adj[v] if alive[u] and deg[u] > d)
            s += 0.5 * rng.random()
            if s > best_s:
                best_s, best_v = s, v
        alive[best_v] = False


def _readd(N, adj, alive, d, D, rng, deadline):
    """Try to re-add deleted vertices in random order, keeping validity."""
    removed = [v for v in range(N) if not alive[v]]
    rng.shuffle(removed)
    for v in removed:
        if time.monotonic() > deadline:
            break
        alive[v] = True
        _, _, tb, ex = _state(N, adj, alive, d, D)
        if tb or ex:
            alive[v] = False
    return alive


def _deletion_search(d, D, seed, deadline):
    """Best valid induced subgraph of PG(2, q), q the smallest prime power >= d. Returns (n, edges) or None."""
    q = next((c for c in range(d, d + 10) if lib.is_prime_power(c)), None)
    if q is None or q > 25:
        return None
    N, edges, adj = _pg_adj(q)
    rng = random.Random(seed * 104729 + d)
    best = None
    while time.monotonic() < deadline:
        alive = _greedy_delete(N, adj, d, D, rng, deadline)
        if alive is None:
            break
        alive = _readd(N, adj, alive, d, D, rng, deadline)
        keep = [v for v in range(N) if alive[v]]
        if len(keep) < 2 or (best is not None and len(keep) <= best[0]):
            continue
        idx = {v: i for i, v in enumerate(keep)}
        E = [(idx[u], idx[v]) for u, v in edges if alive[u] and alive[v]]
        best = (len(keep), E)
    return best


# ----------------------------------------------------------------------------
# Simulated annealing over group voltage lifts (parent, used as a general fallback).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


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


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
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


def _edges_from(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
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
        return _edges_from(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(2.0, min(0.75 * time_limit, time_limit - 8.0))
    deadline = start + budget
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

    if D >= 3:
        for n_c, e_c in _arc_candidates(d, deadline, random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    # Bold new construction for the D = 3, large-d targets: deletion from PG(2, q), q >= d.
    if D == 3 and d >= 10 and time.monotonic() < deadline:
        now = time.monotonic()
        del_deadline = now + 0.8 * (deadline - now)
        res = _deletion_search(d, D, seed, del_deadline)
        if res is not None:
            consider(res[0], res[1])

    # Remaining time: group-lift annealing as a general fallback.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
