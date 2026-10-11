"""Bipartite graphs with max degree d and diameter <= D.

Families:
  * projective-plane incidence graphs and the Araujo-Pardo-Lopez graph (D = 3);
  * unequal bi-orbit voltage lifts over small groups: kA orbits on side A and
    kB >= kA orbits on side B, every A-orbit carrying exactly d darts, B-orbit
    loads capped at d.  Lopsided orbit counts leave spare degree on side B,
    which the cover/saturation growth then uses;
  * cover-based vertex insertion and saturation of spare degree;
  * vertex-deletion repair for near-miss lifts.
"""
import itertools
import math
import random
import time

import lib


_BIG = 10 ** 9
_REPAIR_MAX = 60


# ----------------------------------------------------------------------------
# Baseline families.
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
# Small graph utilities.
# ----------------------------------------------------------------------------

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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy cover of `full` by at most d candidate neighbours; None on failure."""
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


def _extend_cover(n, edges, d, D, deadline, rng, randomize=False):
    """Add vertices whose (deficient) neighbourhoods cover everything within D-1."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = _adj_from(n, edges)
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
                chosen = _greedy_cover(cands, ball, full, d, rng, randomize or attempt > 0)
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
    """Join deficient opposite-side vertices in random order (only adds edges)."""
    edges = list(edges)
    adj = _adj_from(n, edges)
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


def _grow(n, edges, d, D, deadline, rng):
    """Alternate cover-vertex insertion and saturation while it keeps growing."""
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


# ----------------------------------------------------------------------------
# Unequal bi-orbit voltage lifts over finite groups.
#
# Side A has kA orbits A_{i,g}, side B has kB orbits B_{j,h}, each orbit of
# size G = |group|.  Each A-orbit i carries exactly d darts (i, j, s); a dart
# joins A_{i,g} to B_{j, g*s} for all g.  B-orbit j receives cnt[j] <= d darts,
# so B-degrees are at most d.  Left multiplication is an automorphism, so the
# reach from one representative per orbit decides validity.  kB > kA leaves
# spare degree on side B for later cover growth.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """(order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    choices = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12]
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


def _random_darts(d, kA, kB, G, rng):
    cnt = [0] * kB
    darts = []
    for i in range(kA):
        for _ in range(d):
            opts = [j for j in range(kB) if cnt[j] < d]
            j = rng.choice(opts)
            cnt[j] += 1
            darts.append([i, j, rng.randrange(G)])
    return darts


def _loads_ok(darts, kB, d):
    cnt = [0] * kB
    for x in darts:
        cnt[x[1]] += 1
        if cnt[x[1]] > d:
            return False
    return True


def _perm_of(cache, mul, G, s):
    p = cache.get(s)
    if p is None:
        p = [mul(g, s) for g in range(G)]
        cache[s] = p
    return p


def _unequal_cost(kA, kB, G, D, darts, perms, limit=float("inf")):
    """Unreached (orbit representative, vertex) pairs within distance D; 0 means valid."""
    if len({(x[0], x[1], x[2]) for x in darts}) < len(darts):
        return _BIG
    N = (kA + kB) * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ai = i * G
        bj = (kA + j) * G
        for g in range(G):
            a = ai + g
            b = bj + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(kA)] + [(kA + j) * G for j in range(kB)]
    total = 0
    for src in reps:
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
        if total > limit:
            return total
    return total


def _unequal_edges(kA, kB, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (kA + j) * G + pm[g]))
    return (kA + kB) * G, sorted(E)


def _anneal_unequal(d, D, kA, kB, G, mul, rng, deadline, iters):
    """Anneal darts (voltages, B-targets) until the lift has diameter <= D.

    Returns (edges_or_None, darts, cost).
    """
    cache = {}
    darts = _random_darts(d, kA, kB, G, rng)
    cost = _unequal_cost(kA, kB, G, D, darts,
                         [_perm_of(cache, mul, G, x[2]) for x in darts])
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.996)
        limit = cost - T * math.log(1.0 - rng.random())
        cand = [list(x) for x in darts]
        r = rng.random()
        if r < 0.5:
            cand[rng.randrange(len(cand))][2] = rng.randrange(G)
        elif r < 0.8:
            cand[rng.randrange(len(cand))][1] = rng.randrange(kB)
        else:
            a = rng.randrange(len(cand))
            b = rng.randrange(len(cand))
            cand[a][1], cand[b][1] = cand[b][1], cand[a][1]
        if not _loads_ok(cand, kB, d):
            continue
        c2 = _unequal_cost(kA, kB, G, D, cand,
                           [_perm_of(cache, mul, G, x[2]) for x in cand], limit)
        if c2 <= limit:
            darts, cost = cand, c2
    if cost == 0:
        perms = [_perm_of(cache, mul, G, x[2]) for x in darts]
        N, E = _unequal_edges(kA, kB, G, darts, perms)
        return (N, E), darts, 0
    return None, darts, cost


def _lift_edges(kA, kB, G, mul, darts):
    cache = {}
    perms = [_perm_of(cache, mul, G, x[2]) for x in darts]
    return _unequal_edges(kA, kB, G, darts, perms)


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))   # K_{d,d}: diameter 2, valid for D >= 2
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
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.1 * time_limit, rng)
            consider(n2, e2)
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Unequal bi-orbit lifts for D >= 3 and d >= 3.
    if D >= 3 and d >= 3:
        while time.monotonic() < deadline and best_n < moore:
            kA = rng.choice([1, 1, 2, 2, 3])
            kB = kA + (1 if rng.random() < 0.2 else 0)
            tot = kA + kB
            lo = best_n // tot + 1
            hi = lo + max(2, lo // 8)
            G = rng.randint(lo, hi)
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res, darts, c = _anneal_unequal(d, D, kA, kB, order, mul, rng, deadline, 600)
            if res is not None:
                n, e = res
                e = _saturate_edges(n, e, d, rng)
                consider(n, e)
                n2, e2 = _grow(n, e, d, D, min(deadline, time.monotonic() + 3.0), rng)
                consider(n2, e2)
                continue
            if c <= _REPAIR_MAX and rng.random() < 0.3 and time.monotonic() < deadline:
                N, E = _lift_edges(kA, kB, order, mul, darts)
                rep = _repair(N, E, D, min(deadline, time.monotonic() + 3.0), rng)
                if rep is not None:
                    n, e = rep
                    e = _saturate_edges(n, e, d, rng)
                    consider(n, e)
                    n2, e2 = _grow(n, e, d, D, min(deadline, time.monotonic() + 2.0), rng)
                    consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
