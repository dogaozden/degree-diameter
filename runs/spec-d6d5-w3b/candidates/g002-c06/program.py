import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Constants and small helpers.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
_REPAIR_MAX_COST = 60


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _adj_from(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bipartition(n, adj):
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


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


# ----------------------------------------------------------------------------
# NEW HELPER: matrix-based representative-orbit cost.
#
# A semidirect/cyclic voltage lift is invariant under left multiplication by
# the group, so every layer is a single orbit and only the identity vertex of
# each of the 2k layers needs a BFS. Instead of one Python BFS per
# representative, all 2k representatives are advanced together: the reach
# sets form a (2k x N) boolean matrix that is multiplied by the (N x N)
# adjacency matrix once per distance step (float32 BLAS).
# ----------------------------------------------------------------------------

def _cost_np(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    A = np.zeros((N, N), dtype=np.float32)
    ar = np.arange(G, dtype=np.int64)
    for (i, j, _s), pm in zip(darts, perms):
        a = i * G + ar
        b = (k + j) * G + np.asarray(pm, dtype=np.int64)
        A[a, b] = 1.0
        A[b, a] = 1.0
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    R = len(reps)
    seen = np.zeros((R, N), dtype=bool)
    seen[np.arange(R), reps] = True
    frontier = seen.astype(np.float32)
    for _ in range(D):
        nxt = (frontier @ A) > 0
        nxt &= ~seen
        if not nxt.any():
            break
        seen |= nxt
        frontier = nxt.astype(np.float32)
    return R * N - int(seen.sum())


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


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


def _sample_group(G, rng, choices):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
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


def _anneal(d, D, k, G, mul, rng, deadline, iters, start_darts=None, T0=1.0):
    """Metropolis annealing over voltages and B-assignments using the matrix cost."""
    if start_darts is None:
        darts = _random_darts(d, k, G, rng)
    else:
        darts = [list(x) for x in start_darts]
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost_np(k, G, D, darts, perms)

    T = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost_np(k, G, D, darts, perms)
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
            c2 = _cost_np(k, G, D, darts, perms)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms), darts, 0
    return None, darts, cost


# ----------------------------------------------------------------------------
# Repair by deleting far-off vertices, then saturating spare degree.
# ----------------------------------------------------------------------------

def _compact(n, edges, keep):
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    E = [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]
    return len(new), E


def _repair(n, edges, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        if cur_n == 0:
            return None
        adj = _adj_from(cur_n, cur_e)
        ball = _balls_radius(cur_n, adj, D)
        bad = [cur_n - b.bit_count() for b in ball]
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


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices (only adds edges)."""
    edges = list(edges)
    adj = _adj_from(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
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


def _lift_repair(d, D, k, G, mul, darts, deadline, rng):
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    N, E = _edges(k, G, darts, perms)
    rep = _repair(N, E, D, deadline, rng)
    if rep is None:
        return None
    n, e = rep
    e = _saturate_edges(n, e, d, rng)
    return n, e


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.9 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Bi-Cayley voltage lift search over semidirect products.
    if D >= 3 and d >= 3:
        ks = [1, 1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
        all_k2 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
        elite = {}
        while time.monotonic() < deadline and best_n < moore:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            lo = max(2, base + 1)
            if k == 1:
                hi = lo + max(3, lo // 4)
            else:
                hi = lo + max(3, lo // 8)
            G = rng.randint(lo, hi)
            g = None
            if rng.random() < 0.8:
                g = _sample_group(G, rng, k2_pool)
            if g is None:
                g = _sample_group(G, rng, all_k2)
            if g is None:
                continue
            order, mul = g
            key = (k, order)

            start_darts, T0 = None, 1.0
            mul_use = mul
            if key in elite and rng.random() < 0.5:
                _, st, mul_use = elite[key]
                start_darts = _perturb(st, order, rng, rng.randint(1, 3))
                T0 = 0.5

            iters = 1500 if k == 1 else 400
            res, darts_out, c = _anneal(d, D, k, order, mul_use, rng, deadline,
                                        iters, start_darts, T0)
            if res is not None:
                consider(res[0], res[1])
                continue

            if key not in elite or c < elite[key][0]:
                elite[key] = (c, darts_out, mul_use)

            if c <= _REPAIR_MAX_COST and rng.random() < 0.35 and time.monotonic() < deadline:
                rep_deadline = min(deadline, time.monotonic() + 4.0)
                out = _lift_repair(d, D, k, order, mul_use, darts_out, rep_deadline, rng)
                if out is not None:
                    consider(out[0], out[1])

    # Spend remaining spare degree on the final graph.
    if best_n < moore:
        e_sat = _saturate_edges(best[0], best[1], d, rng)
        consider(best[0], e_sat)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
