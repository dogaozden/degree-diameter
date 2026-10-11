import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane baseline (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (capped for speed)."""
    for q in range(min(d - 1, 31), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2, searched by annealing
# on the number of bad pairs. Any near-valid lift that is too large is then
# repaired by deleting the most-offending vertices and re-saturating degrees.
#
# Vertices: A_{i,g} = i*G + g (colour 0) and B_{j,h} = (k+j)*G + h (colour 1).
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for every g in the group.
# Each layer L of d layers contributes one dart per source i, with target
# p_L[i], so every vertex has degree exactly d.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product of order G, or None."""
    divs = [k2 for k2 in range(1, 13) if G % k2 == 0 and G // k2 >= 2]
    if not divs:
        return None
    for _ in range(40):
        k2 = rng.choice(divs)
        m = G // k2
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in range(1, m)
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


def _lift_adj(k, G, T, spec):
    """Adjacency lists of the lift described by spec = [(i, j, s), ...]."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in spec:
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + T[g][s]
            adj[a].append(b)
            adj[b].append(a)
    return N, adj


def _bad_pairs_adj(N, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        nxt = [0] * N
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt[v] = x
        ball = nxt
    return sum(N - b.bit_count() for b in ball) // 2


def _anneal(d, D, k, G, T, rng, deadline, iters):
    """Simulated annealing over voltages and target permutations; returns (best_spec, best_cost)."""
    spec = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            spec.append([i, p[i], rng.randrange(G)])

    def score(sp):
        if len({(a, b, c) for a, b, c in sp}) < len(sp):
            return _BIG  # duplicate dart would create a multi-edge
        N, adj = _lift_adj(k, G, T, sp)
        return _bad_pairs_adj(N, adj, D)

    cost = score(spec)
    best_cost = cost
    best_spec = [row[:] for row in spec]
    T0 = max(2.0, 0.05 * cost) if cost < _BIG else 5.0
    T_end = 0.3

    for it in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (T_end / T0) ** (it / max(1, iters))
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(spec))
            old = spec[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            spec[idx][2] = new
            c2 = score(spec)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                spec[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            spec[ia][1], spec[ib][1] = spec[ib][1], spec[ia][1]
            c2 = score(spec)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                spec[ia][1], spec[ib][1] = spec[ib][1], spec[ia][1]
        if cost < best_cost:
            best_cost = cost
            best_spec = [row[:] for row in spec]
    return best_spec, best_cost


# ----------------------------------------------------------------------------
# Repair: delete the vertices covering the most bad pairs, re-saturating
# degrees after every deletion. Deletions keep the bipartition, and
# saturation only adds edges between opposite colours, so distances can
# only shrink relative to the deleted-graph state.
# ----------------------------------------------------------------------------

def _saturate_sets(alive, adjs, color, d, rng):
    """Greedily add edges between deficient opposite-colour alive vertices."""
    left = [v for v in alive if color[v] == 0 and len(adjs[v]) < d]
    right = [v for v in alive if color[v] == 1 and len(adjs[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adjs[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adjs[a]) < d and len(adjs[b]) < d and b not in adjs[a]:
            adjs[a].add(b)
            adjs[b].add(a)


def _repair(N, adj, color, d, D, min_alive, rng, deadline):
    """Return (n, edges) of a repaired graph with at least min_alive vertices, or None."""
    adjs = [set(a) for a in adj]
    alive = list(range(N))
    _saturate_sets(alive, adjs, color, d, rng)
    while True:
        if time.monotonic() > deadline:
            return None
        ball = {v: 1 << v for v in alive}
        for _ in range(D):
            nxt = {}
            for v in alive:
                x = ball[v]
                for u in adjs[v]:
                    x |= ball[u]
                nxt[v] = x
            ball = nxt
        m = len(alive)
        bad = {v: m - ball[v].bit_count() for v in alive}
        if sum(bad.values()) == 0:
            break
        if m - 1 < min_alive:
            return None
        mx = max(bad.values())
        v = rng.choice([x for x in alive if bad[x] == mx])
        for u in adjs[v]:
            adjs[u].discard(v)
        adjs[v] = set()
        alive.remove(v)
        _saturate_sets(alive, adjs, color, d, rng)
    idx = {v: i for i, v in enumerate(alive)}
    edges = sorted({(min(idx[a], idx[b]), max(idx[a], idx[b]))
                    for a in alive for b in adjs[a]})
    return len(alive), edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search (D >= 4): annealed bi-Cayley lifts with repair of near-misses.
    if D >= 4:
        while time.monotonic() < deadline:
            target = best_n + 2
            k = rng.choice([1, 1, 2, 2, 3, 4])
            G = max(2, -(-target // (2 * k)) + rng.randrange(0, 4))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            T = [[mul(x, y) for y in range(order)] for x in range(order)]
            spec, c = _anneal(d, D, k, order, T, rng, deadline, iters=1200)
            if c >= _BIG:
                continue
            N, adj = _lift_adj(k, order, T, spec)
            if c == 0:
                edges = [(a, b) for a in range(N) for b in adj[a] if a < b]
                consider(N, edges)
            else:
                color = [0 if v < k * order else 1 for v in range(N)]
                res = _repair(N, adj, color, d, D, best_n + 1, rng, deadline)
                if res is not None:
                    consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
