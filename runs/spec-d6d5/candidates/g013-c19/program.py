import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline: projective plane incidence graph, grown by cover/saturation.
# K_{d,d} / cycle / Moore-optimal cases return early.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
_K_CHOICES = [1, 1, 2, 2, 3, 3, 4, 6]
_K2_CHOICES = [1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
_ITERS = 2500
_REPAIR_MAX_COST = 120


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(60):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


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


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(6):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Diameter repair by vertex deletion.
# ----------------------------------------------------------------------------

def _compact(n, edges, keep):
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    E = [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]
    return len(new), E


def _repair(n, edges, D, deadline, rng):
    """Delete far-off vertices in batches until diameter <= D. Returns (n, edges) or None."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        if cur_n == 0:
            return None
        adj = [[] for _ in range(cur_n)]
        for u, v in cur_e:
            adj[u].append(v)
            adj[v].append(u)
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


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 with a numpy BFS.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g. Left translation by
# any group element is an automorphism, so distances from A_i,e and B_j,e
# (k + k reps) determine the whole diameter.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice(_K2_CHOICES)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            order, mul, _ = lib.semidirect_group(m, 1, 1)
            return order, mul
        cands = [r for r in rng.sample(range(1, m), min(m - 1, 80))
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not cands:
            continue
        r = rng.choice(cands)
        order, mul, _ = lib.semidirect_group(m, k2, r)
        return order, mul
    return None


def _inv(p):
    """Inverse of a permutation given as an int64 array."""
    q = np.empty_like(p)
    q[p] = np.arange(p.size, dtype=p.dtype)
    return q


def _cost_np(k, G, D, darts, perms, invs, limit):
    """Total number of (representative, vertex) pairs at distance > D. Zero means valid.

    Returns early with a value above `limit` once the running total exceeds it.
    """
    seen = set()
    for i, j, s in darts:
        key = (i, j, s)
        if key in seen:
            return _BIG
        seen.add(key)
    A_out = [[] for _ in range(k)]
    B_out = [[] for _ in range(k)]
    for t, (i, j, _s) in enumerate(darts):
        A_out[i].append((j, perms[t]))
        B_out[j].append((i, invs[t]))
    N = 2 * k * G
    total = 0
    for side in (0, 1):
        for t0 in range(k):
            RA = np.zeros((k, G), dtype=bool)
            RB = np.zeros((k, G), dtype=bool)
            if side == 0:
                RA[t0, 0] = True
                FA = RA.copy()
                FB = np.zeros((k, G), dtype=bool)
            else:
                RB[t0, 0] = True
                FB = RB.copy()
                FA = np.zeros((k, G), dtype=bool)
            for _ in range(D):
                NA = np.zeros((k, G), dtype=bool)
                NB = np.zeros((k, G), dtype=bool)
                for i in range(k):
                    idx = np.flatnonzero(FA[i])
                    if idx.size:
                        for j, p in A_out[i]:
                            NB[j, p[idx]] = True
                for j in range(k):
                    idx = np.flatnonzero(FB[j])
                    if idx.size:
                        for i, q in B_out[j]:
                            NA[i, q[idx]] = True
                NA &= ~RA
                NB &= ~RB
                RA |= NA
                RB |= NB
                FA, FB = NA, NB
                if not (FA.any() or FB.any()):
                    break
            total += N - int(RA.sum()) - int(RB.sum())
            if total > limit:
                return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), p in zip(darts, perms):
        A = i * G + np.arange(G, dtype=np.int64)
        B = (k + j) * G + p
        E.update(zip(A.tolist(), B.tolist()))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters, start=None, T0=1.0):
    """Simulated annealing over voltages and per-layer B-assignments.

    Returns (darts, perms, cost). Metropolis acceptance: a move with new cost c2
    is accepted iff c2 <= cost - T*ln(u), u ~ Uniform(0, 1].
    """
    cache = {}

    def perm_of(s):
        p = cache.get(s)
        if p is None:
            p = np.array([mul(g, s) for g in range(G)], dtype=np.int64)
            cache[s] = p
        return p

    if start is None:
        darts = []
        for _ in range(d):
            p = rng.sample(range(k), k)
            for i in range(k):
                darts.append([i, p[i], rng.randrange(G)])
    else:
        darts = [list(x) for x in start]
    perms = [perm_of(s) for _, _, s in darts]
    invs = [_inv(p) for p in perms]
    cost = _cost_np(k, G, D, darts, perms, invs, float("inf"))

    T = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())

        if k == 1 or rng.random() < 0.6:
            t = rng.randrange(len(darts))
            old_s = darts[t][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_p, old_q = perms[t], invs[t]
            darts[t][2] = new_s
            perms[t] = perm_of(new_s)
            invs[t] = _inv(perms[t])
            c2 = _cost_np(k, G, D, darts, perms, invs, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[t][2] = old_s
                perms[t], invs[t] = old_p, old_q
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost_np(k, G, D, darts, perms, invs, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    return darts, perms, cost


def _perturb(darts, G, rng, flips):
    out = [list(x) for x in darts]
    for _ in range(flips):
        out[rng.randrange(len(out))][2] = rng.randrange(G)
    return out


def _lift_repair(d, D, k, G, darts, perms, deadline, rng):
    """Build the lift, delete far-off vertices until diameter <= D, then saturate."""
    N, E = _edges(k, G, darts, perms)
    rep = _repair(N, E, D, deadline, rng)
    if rep is None:
        return None
    n, e = rep
    e = _saturate_edges(n, e, d, rng)
    return n, e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d == 2 and D >= 2:
        consider(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.1 * time_limit, rng)
            consider(n2, e2)

    # Calibration cases already at the Moore bound return immediately.
    if D < 3 or d < 3 or best_n >= lib._moore_bound(d, D):
        return best

    # Main search: annealed bi-Cayley lifts with numpy BFS, elite warm starts,
    # and repair of near-miss lifts by vertex deletion.
    elite = {}
    while time.monotonic() < deadline:
        k = rng.choice(_K_CHOICES)
        lo = max(3, best_n // (2 * k) + 1)
        hi = lo + max(2, lo // 4)
        G = rng.randint(lo, hi)
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

        darts, perms, c = _anneal(d, D, k, order, mul_use, rng, deadline,
                                  _ITERS, start_darts, T0)

        if c == 0:
            n, e = _edges(k, order, darts, perms)
            consider(n, e)
            n3, e3 = _grow(n, e, d, D, min(deadline, time.monotonic() + 3.0), rng)
            consider(n3, e3)
            continue

        if key not in elite or c < elite[key][0]:
            elite[key] = (c, darts, mul_use)

        if c <= _REPAIR_MAX_COST and rng.random() < 0.5 and time.monotonic() < deadline:
            rep_deadline = min(deadline, time.monotonic() + 4.0)
            out = _lift_repair(d, D, k, order, darts, perms, rep_deadline, rng)
            if out is not None:
                consider(out[0], out[1])
                n3, e3 = _grow(out[0], out[1], d, D,
                               min(deadline, time.monotonic() + 3.0), rng)
                consider(n3, e3)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
