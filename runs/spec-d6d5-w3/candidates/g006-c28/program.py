import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Small graph utilities.
# ----------------------------------------------------------------------------

def _adj(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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


def _compact(n, edges, keep):
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    return len(new), [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]


def _repair(n, edges, D, deadline, rng):
    """Delete the vertices with the most far-off partners until diameter <= D."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        if cur_n == 0:
            return None
        adj = _adj(cur_n, cur_e)
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


def _saturate(n, edges, d, rng):
    """Add cross-side edges between deficient vertices. Adding edges never breaks diameter or bipartiteness."""
    edges = list(edges)
    adj = _adj(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
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
    return n, edges


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k.
#
# Layout: A_i,g = i*G + g, B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g.
# Layer L consists of darts darts[L*k:(L+1)*k]; within a layer each i and each j
# appears exactly once, so every vertex has degree d.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
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


def _cost(k, G, D, darts, perms, limit=float("inf")):
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
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _greedy_darts(d, k, G, D, mul, rng, samples):
    """Constructive phase: fill each layer one A-vertex at a time, choosing the (j, voltage)
    pair that minimises the unreached-pair count among a random sample of voltages."""
    darts, perms = [], []
    seen = set()
    for _layer in range(d):
        used = set()
        order = list(range(k))
        rng.shuffle(order)
        for i in order:
            best = None
            for j in range(k):
                if j in used:
                    continue
                for _ in range(samples):
                    s = rng.randrange(G)
                    if (i, j, s) in seen:
                        continue
                    pm = _right_perm(mul, G, s)
                    darts.append([i, j, s])
                    perms.append(pm)
                    c = _cost(k, G, D, darts, perms)
                    darts.pop()
                    perms.pop()
                    if best is None or c < best[0]:
                        best = (c, j, s, pm)
            if best is None:
                j = min(x for x in range(k) if x not in used)
                s = rng.randrange(G)
                pm = _right_perm(mul, G, s)
            else:
                _, j, s, pm = best
            darts.append([i, j, s])
            perms.append(pm)
            seen.add((i, j, s))
            used.add(j)
    return darts, perms


def _anneal(d, D, k, G, mul, rng, deadline, iters, darts, perms, T0):
    """Simulated annealing over voltages and within-layer B-assignments. Returns final cost."""
    cost = _cost(k, G, D, darts, perms)
    T = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            oldp = perms[idx]
            darts[idx][2] = new
            perms[idx] = _right_perm(mul, G, new)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old
                perms[idx] = oldp
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return cost


# ----------------------------------------------------------------------------
# Baseline families (safe fallbacks, valid for D >= 3).
# ----------------------------------------------------------------------------

def _baseline(d, consider):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            n, e = lib.projective_plane_incidence(q)
            consider(n, e)
            break
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            n, e = lib.araujo_lopez_graph(q)
            consider(n, e)
        except Exception:
            pass


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    target = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        _baseline(d, consider)
    if best_n >= target:
        return best

    # Main search: greedy-seeded, annealed voltage lifts over non-cyclic groups,
    # with repair of near-miss lifts followed by saturation.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 2, 3]
    try:
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            lo = max(2, base + 1)
            hi = lo + max(3, lo // 6)
            G = rng.randint(lo, hi)
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            samples = 6 if k <= 2 else 3
            iters = 1200 if k == 1 else 500

            darts, perms = _greedy_darts(d, k, order, D, mul, rng, samples)
            if time.monotonic() > deadline:
                break
            cost = _anneal(d, D, k, order, mul, rng, deadline, iters, darts, perms, 0.7)
            N, E = _edges(k, order, darts, perms)

            if cost == 0:
                consider(N, E)
                if best_n >= target:
                    break
                continue

            if cost <= 60 and time.monotonic() < deadline:
                rep_deadline = min(deadline, time.monotonic() + 4.0)
                rep = _repair(N, E, D, rep_deadline, rng)
                if rep is not None:
                    n3, e3 = _saturate(rep[0], rep[1], d, rng)
                    consider(n3, e3)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
