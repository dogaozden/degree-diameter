import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Graph utilities
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
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


def _balls(n, adj, r):
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
# Diameter-preserving growth: new vertex joins one side and covers everything
# within distance D of the graph. Then spare degree is used for extra edges.
# ----------------------------------------------------------------------------

def _cover(cands, ball, full, d, rng):
    """Greedy cover of `full` by at most d candidates (balls of radius D-1). None on failure."""
    pool = list(cands)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best = max(gains)
        if best == 0:
            break
        opts = [i for i, g in enumerate(gains) if g == best]
        i = rng.choice(opts)
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _saturate(n, edges, d, rng):
    """Join deficient opposite-side vertices. Keeps bipartiteness and only shortens distances."""
    edges = list(edges)
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    existing = {(min(u, v), max(u, v)) for u, v in edges}
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
    return n, edges


def _grow(n, edges, d, D, deadline, rng):
    if D < 2:
        return n, list(edges)
    edges = list(edges)
    while time.monotonic() < deadline:
        adj = _adjacency(n, edges)
        deg = [len(a) for a in adj]
        color = _bipartition(n, adj)
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            chosen = _cover(cands, ball, full, d, rng)
            if chosen:
                v = n
                n += 1
                for s in chosen:
                    edges.append((s, v))
                added = True
                break
        if not added:
            break
    return _saturate(n, edges, d, rng)


# ----------------------------------------------------------------------------
# Projective plane base (D >= 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over Z_m x| Z_k, searched by annealing.
#
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,g*s for every g.
# Each A-layer and each B-layer receives exactly d darts, so the lift is d-regular.
# The cost is the total number of vertex pairs at distance > D, computed with
# bitsets over all vertices. Zero means the lift has diameter <= D.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    ks = [k for k in (1, 2, 3, 4, 5, 6, 8, 9, 10, 12) if G % k == 0 and G // k >= 2]
    if not ks:
        return None
    for _ in range(30):
        k2 = rng.choice(ks)
        m = G // k2
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in range(1, m)
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        order, mul, _ = lib.semidirect_group(m, k2, r)
        return order, mul
    return None


def _lift_cost(k, G, D, darts, perms):
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
    balls = _balls(N, adj, D)
    return sum(N - b.bit_count() for b in balls)


def _lift_edges(k, G, darts, perms):
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
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)

    T0, T_end = 2.0, 0.2
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T_end / T0) ** (it / max(1, iters))

        if rng.random() < 0.75 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_pm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = [mul(g, new_s) for g in range(G)]
            c2 = _lift_cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_pm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _lift_cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _lift_edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Main entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = (fb_n, list(fb_e))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.2 * time_limit, rng)
                consider(n2, e2)

        main_deadline = start + 0.82 * time_limit
        if D >= 4:
            ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 2, 3]
            iters = 1500 if D >= 5 else 400
            while time.monotonic() < main_deadline:
                k = rng.choice(ks)
                G = best[0] // (2 * k) + 1 + rng.randrange(0, 3)
                grp = _sample_group(G, rng)
                if grp is None:
                    continue
                order, mul = grp
                res = _anneal(d, D, k, order, mul, rng, main_deadline, iters)
                if res is not None:
                    n, e = res
                    consider(n, e)
                    gn, ge = _grow(n, e, d, D, main_deadline, rng)
                    consider(gn, ge)

        # Tail: grow the current best once more with the remaining margin.
        gn, ge = _grow(best[0], best[1], d, D, start + 0.9 * time_limit, rng)
        consider(gn, ge)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        fb_n, fb_e = lib.haar_graph(d, range(d))
        return fb_n, list(fb_e)
    return best
