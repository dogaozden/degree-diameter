import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Graph utilities.
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
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


# ----------------------------------------------------------------------------
# New family: bi-Cayley lifts over Z_m x| Z_k2, built by GREEDY layer addition.
#
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# A "layer" is a perfect matching of the k A-blocks to the k B-blocks, each
# given by a voltage s, so every vertex gains exactly one neighbour per layer.
# With d layers the max degree is d. Left multiplication is an automorphism
# that is transitive on each block, so only one representative per block
# needs a BFS when counting pairs at distance > D.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (order, mul), or None."""
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


def _bad_pairs(k, G, darts, D):
    """Number of (block representative, vertex) pairs not within distance D.

    darts is a list of (i, j, perm) where perm[g] gives the B-index of A-element g.
    Zero means every block representative reaches the whole graph within D.
    """
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, pm in darts:
        bi = i * G
        bj = (k + j) * G
        for g in range(G):
            a = bi + g
            b = bj + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for blk in range(2 * k):
        src = blk * G
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _lift_edges(k, G, darts):
    E = set()
    for i, j, pm in darts:
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return sorted(E)


def _greedy_lift(d, D, k, G, mul, rng, deadline, trials):
    """Add d layers, each chosen as the best of `trials` random matchings with voltages.

    Returns (n, edges, cost) where cost is the remaining bad-pair count, or None on timeout.
    """
    perm_cache = {}

    def perm(s):
        if s not in perm_cache:
            perm_cache[s] = [mul(g, s) for g in range(G)]
        return perm_cache[s]

    layers = []
    used = set()
    last_c = None
    for _ in range(d):
        best, best_c = None, None
        for _t in range(trials):
            if time.monotonic() > deadline:
                return None
            p = [0] if k == 1 else rng.sample(range(k), k)
            cand = [(i, p[i], rng.randrange(G)) for i in range(k)]
            if any(x in used for x in cand):
                continue
            darts = [(i, j, perm(s)) for L in layers + [cand] for (i, j, s) in L]
            c = _bad_pairs(k, G, darts, D)
            if best_c is None or c < best_c:
                best, best_c = cand, c
                if c == 0:
                    break
        if best is None:
            return None
        layers.append(best)
        used.update(best)
        last_c = best_c
    darts = [(i, j, perm(s)) for L in layers for (i, j, s) in L]
    return 2 * k * G, _lift_edges(k, G, darts), last_c


# ----------------------------------------------------------------------------
# Repair by vertex deletion and saturation by adding edges (both keep validity
# checks to the caller).
# ----------------------------------------------------------------------------

def _repair(n, edges, D, deadline, rng):
    """Delete far-off vertices in batches until the diameter is <= D. Returns (n, edges) or None."""
    cur_n, cur_e = n, list(edges)
    while cur_n > 0 and time.monotonic() < deadline:
        adj = _adjacency(cur_n, cur_e)
        ball = _balls_radius(cur_n, adj, D)
        bad = [cur_n - b.bit_count() for b in ball]
        if not any(bad):
            return cur_n, cur_e
        bad_v = [v for v in range(cur_n) if bad[v] > 0]
        rng.shuffle(bad_v)
        bad_v.sort(key=lambda v: -bad[v])
        batch = max(1, len(bad_v) // 12)
        dead = set(bad_v[:batch])
        new = {}
        for v in range(cur_n):
            if v not in dead:
                new[v] = len(new)
        cur_e = [(new[u], new[v]) for u, v in cur_e if u in new and v in new]
        cur_n = len(new)
    return None


def _saturate(n, edges, d, rng):
    """Add random opposite-side edges between deficient vertices (only lowers distances)."""
    edges = list(edges)
    adj = _adjacency(n, edges)
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
    return edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 5 and d >= 3:
        try:
            while time.monotonic() < deadline:
                k = rng.choice([1, 1, 2, 2, 3, 4])
                lo = best_n // (2 * k) + 1
                hi = lo + max(3, lo // 4)
                G = rng.randint(max(2, lo), hi)
                g = _sample_group(G, rng)
                if g is None:
                    continue
                order, mul = g
                res = _greedy_lift(d, D, k, order, mul, rng,
                                   min(deadline, time.monotonic() + 12.0), 30)
                if res is None:
                    continue
                n, e, c = res
                if c == 0:
                    consider(n, e)
                    continue
                if c <= 300 and time.monotonic() < deadline:
                    out = _repair(n, e, D, min(deadline, time.monotonic() + 4.0), rng)
                    if out is not None:
                        n2, e2 = out
                        e2 = _saturate(n2, e2, d, rng)
                        consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
