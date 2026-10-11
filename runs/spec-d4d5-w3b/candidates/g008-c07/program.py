import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Bitmask ball helpers.
# ----------------------------------------------------------------------------

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


def _cover(cands, ball, full, d, rng, randomize):
    """Greedy cover of `full` by at most d candidates, each contributing its ball."""
    pool = list(cands)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.3:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


# ----------------------------------------------------------------------------
# Growth: add vertices whose neighbourhoods cover everything within D-1,
# then saturate remaining spare degree with extra edges. Both steps keep the
# graph bipartite and diameter <= D, so no re-check is needed in principle.
# ----------------------------------------------------------------------------

def _grow(n, edges, color, d, D, deadline, rng):
    edges = list(edges)
    color = list(color)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]

    while time.monotonic() < deadline and D >= 2:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        sides = [0, 1]
        rng.shuffle(sides)
        added = False
        for c in sides:
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(40):
                if time.monotonic() >= deadline:
                    break
                chosen = _cover(cands, ball, full, d, rng, attempt > 0)
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

    # Saturate: join deficient opposite-side pairs (only shortens distances).
    existing = set((min(u, v), max(u, v)) for u, v in edges)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d and (min(a, b), max(a, b)) not in existing:
            edges.append((a, b))
            existing.add((min(a, b), max(a, b)))
            deg[a] += 1
            deg[b] += 1
    return n, edges


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k, annealed.
# Vertices: A_{i,g} = i*G + g, B_{j,h} = (k+j)*G + h.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for all g.
# Each layer L contributes one dart per A-layer i, so every vertex has degree d.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6])
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


def _cost(k, G, D, darts, perms):
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


def _edges(k, G, darts, perms):
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
            perms[idx] = [mul(g, new_s) for g in range(G)]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
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
            if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Seed constructions.
# ----------------------------------------------------------------------------

def _pg_seed(d, D):
    """Incidence graph of PG(2,q) for the largest prime power q <= d-1 (diameter 3)."""
    if D < 3:
        return None
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            n, e = lib.projective_plane_incidence(q)
            m = n // 2
            color = [0] * m + [1] * m
            return n, e, color
    return None


def _search_lifts(d, D, deadline, rng, consider, best_n):
    """Anneal bi-Cayley lifts with orders just above the current best."""
    ks = [1, 2, 2, 3, 3, 4, 5, 6] if D >= 5 else [1, 2, 3]
    iters = 1500 if D >= 5 else 600
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n() // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, 4))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters)
        if res is None:
            continue
        n, e = res
        color = [0] * (k * order) + [1] * (k * order)
        consider(n, e)
        gn, ge = _grow(n, e, color, d, D, deadline, rng)
        consider(gn, ge)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    state = {"best": fallback}
    bound = lib.moore_bound(d, D)

    def consider(n, e):
        if n > state["best"][0] and lib.is_valid(n, e, d, D):
            state["best"] = (n, e)

    rng = random.Random(seed)
    search_deadline = start + 0.82 * time_limit

    try:
        seed_pg = _pg_seed(d, D)
        if seed_pg is not None:
            n, e, color = seed_pg
            consider(n, e)
            if state["best"][0] < bound:
                gn, ge = _grow(n, e, list(color), d, D, start + 0.25 * time_limit, rng)
                consider(gn, ge)

        # Stop early when the Moore-optimal graph is already in hand.
        if state["best"][0] < bound:
            _search_lifts(d, D, search_deadline, rng, consider,
                          lambda: state["best"][0])
    except Exception:
        pass  # keep the best valid graph found so far

    n, e = state["best"]
    if not lib.is_valid(n, e, d, D):
        return fallback
    return n, e
