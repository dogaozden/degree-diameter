import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Baseline families: projective plane incidence, Araujo-Pardo-Lopez for D = 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Graph helpers.
# ----------------------------------------------------------------------------

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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
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
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,g*s for every g in the group.
# Darts are stored layer-major: dart index = L*k + i for layer L.
# Left multiplication by any group element is an automorphism, so only one
# representative per side needs a BFS.
# ----------------------------------------------------------------------------

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


def _perm(mul, G, s):
    """Permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
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
        if total > limit:
            return total
    return total


def _edges(k, G, mul, darts):
    """Full edge list of the lift."""
    E = set()
    for i, j, s in darts:
        pm = _perm(mul, G, s)
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _random_darts(layers, k, G, rng):
    darts = []
    for _ in range(layers):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _anneal(D, k, G, mul, rng, deadline, iters, darts, layers, T0=1.0):
    """Simulated annealing over voltages and B-assignments, restricted to the given layers.

    Only darts in `layers` may change; the others are frozen. Cost is computed on all
    darts passed in. Returns (cost, darts, perms).
    """
    perms = [_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    cand = [L * k + i for L in layers for i in range(k)]
    if not cand:
        return cost, darts, perms
    T = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
        if k == 1 or rng.random() < 0.7:
            idx = rng.choice(cand)
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.choice(list(layers))
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return cost, darts, perms


def _layer_completion_search(d, D, k, G, mul, rng, deadline, iters):
    """New routine: two-phase search exploiting that extra layers only add edges.

    Phase 1 anneals a (d-1)-layer lift, which is a looser target and easier to
    make small-diameter. Phase 2 appends one fresh layer and anneals only that
    layer while the first d-1 layers stay frozen. Adding a layer never increases
    any distance, so the frozen part keeps its progress.
    """
    if rng.random() < 0.4 or d < 2:
        darts = _random_darts(d, k, G, rng)
        return _anneal(D, k, G, mul, rng, deadline, iters, darts, range(d))
    dl = d - 1
    darts = _random_darts(dl, k, G, rng)
    _, darts, _ = _anneal(D, k, G, mul, rng, deadline, iters // 2, darts, range(dl))
    p = rng.sample(range(k), k)
    darts = darts + [[i, p[i], rng.randrange(G)] for i in range(k)]
    return _anneal(D, k, G, mul, rng, deadline, iters, darts, [dl])


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        moore = lib.moore_bound(d, D)
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
            ar = _araujo(d)
            if ar is not None:
                consider(ar[0], ar[1])
        if best_n >= moore:
            return best

        ks = [1, 1, 2, 2, 3, 4]
        k2_choices = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
        if D >= 3 and d >= 2:
            while time.monotonic() < deadline and best_n < moore:
                k = rng.choice(ks)
                base = best_n // (2 * k)
                lo = max(2, base + 1)
                hi = lo + max(3, lo // 6)
                G = rng.randint(lo, hi)
                g = _sample_group(G, rng, k2_choices)
                if g is None:
                    g = _sample_group(G, rng, [1])
                if g is None:
                    continue
                order, mul = g
                iters = 1500 if k == 1 else 400
                cost, darts, _perms = _layer_completion_search(
                    d, D, k, order, mul, rng, deadline, iters)
                if cost == 0:
                    n, e = _edges(k, order, mul, darts)
                    consider(n, e)
                    continue
                # Near miss: repair the lift by deleting far-off vertices, then saturate.
                if cost <= 60 and rng.random() < 0.35 and time.monotonic() < deadline:
                    N, E = _edges(k, order, mul, darts)
                    rep = _repair(N, E, D, min(deadline, time.monotonic() + 4.0), rng)
                    if rep is not None:
                        n, e = rep
                        e = _saturate_edges(n, e, d, rng)
                        consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
