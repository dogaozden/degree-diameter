import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases: W(q) for D >= 4, PG(2, q) for D = 3.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q): degree q+1, diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    edges = []
    nl = 0
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            for p in L:
                edges.append((p, P + nl))
                for r in L:
                    if p < r:
                        covered.add((p, r))
            nl += 1
    return 2 * P, edges


def _choose_q(d, D):
    """Return (big, small): the smallest prime power q with q+1 >= d (degree too high, to be thinned)
    and the largest prime power q with q+1 <= d (degree slack). None where unavailable."""
    if D not in (3, 4):
        return None, None
    cap = 9 if D >= 4 else 13
    pp = [q for q in range(2, cap + 1) if lib.is_prime_power(q)]
    big = [q for q in pp if q + 1 >= d]
    small = [q for q in pp if q + 1 <= d]
    return (min(big) if big else None), (max(small) if small else None)


def _to_adj(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        if u != v:
            adj[u].add(v)
            adj[v].add(u)
    return adj


def _structured(D, q):
    if D >= 4:
        n, e = _gq_w(q)
    else:
        n, e = lib.projective_plane_incidence(q)
    return _to_adj(n, e)


# ----------------------------------------------------------------------------
# Graph helpers on list-of-sets adjacency.
# ----------------------------------------------------------------------------

def _edges(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _bipartition(adj):
    n = len(adj)
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


def _balls(adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    n = len(adj)
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
# Degree thinning: remove high-degree neighbours (vertex deletion, not edge deletion).
# ----------------------------------------------------------------------------

def _reduce(adj, d, rng):
    adj = [set(s) for s in adj]
    alive = [True] * len(adj)
    for v in range(len(adj)):
        while alive[v] and len(adj[v]) > d:
            u = max(adj[v], key=lambda x: (len(adj[x]), rng.random()))
            alive[u] = False
            for w in adj[u]:
                adj[w].discard(u)
            adj[u] = set()
    return adj, alive


def _repair(adj, alive, D, rng, deadline):
    """Delete the vertices with most bad pairs until diameter <= D. Returns a compact adjacency or None."""
    while time.monotonic() < deadline:
        keep = [v for v in range(len(adj)) if alive[v]]
        m = len(keep)
        if m == 0:
            return None
        idx = {v: i for i, v in enumerate(keep)}
        nadj = [set(idx[u] for u in adj[v] if alive[u]) for v in keep]
        ball = _balls(nadj, D)
        bad = [m - b.bit_count() for b in ball]
        if sum(bad) == 0:
            return nadj
        order = sorted(range(m), key=lambda i: (-bad[i], rng.random()))
        k = max(1, m // 60)
        for i in order[:k]:
            if bad[i] == 0:
                break
            alive[keep[i]] = False
    return None


# ----------------------------------------------------------------------------
# Growth: add vertices whose neighbourhoods cover everything within D-1.
# Adding a vertex never breaks distances, so every step keeps diameter <= D.
# ----------------------------------------------------------------------------

def _cover(cands, ball, full, d, rng, noisy):
    pool = list(cands)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        mx = max(gains)
        if mx <= 0:
            break
        thr = mx
        if noisy and mx > 1 and rng.random() < 0.3:
            thr = mx - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts)
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _grow(adj, d, D, deadline, rng):
    adj = [set(s) for s in adj]
    color = _bipartition(adj)
    while time.monotonic() < deadline:
        n = len(adj)
        full = (1 << n) - 1
        ball = _balls(adj, D - 1)
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [s for s in range(n) if color[s] == c and len(adj[s]) < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(12):
                chosen = _cover(cands, ball, full, d, rng, attempt > 0)
                if chosen or time.monotonic() > deadline:
                    break
            if chosen:
                v = n
                adj.append(set(chosen))
                for s in chosen:
                    adj[s].add(v)
                color.append(1 - c)
                added = True
                break
        if not added:
            break
    return adj


def _saturate(adj, d, rng):
    """Add edges between deficient opposite-side vertices. Distances only shrink."""
    adj = [set(s) for s in adj]
    color = _bipartition(adj)
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)
    return adj


def _complete(adj, d, D, deadline, rng):
    adj = _grow(adj, d, D, deadline, rng)
    adj = _saturate(adj, d, rng)
    return _grow(adj, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Large-neighbourhood search: delete a few random vertices, repair, regrow.
# ----------------------------------------------------------------------------

def _lns(adj, d, D, deadline, rng, consider):
    cur = [set(s) for s in adj]
    best = [set(s) for s in adj]
    best_n = len(best)
    while time.monotonic() < deadline:
        n = len(cur)
        k = min(rng.choice((1, 1, 2, 2, 3, 4, 6)), n - 1)
        if k < 1:
            break
        alive = [True] * n
        for v in rng.sample(range(n), k):
            alive[v] = False
        res = _repair(cur, alive, D, rng, deadline)
        if res is None:
            break
        new = _complete(res, d, D, deadline, rng)
        m = len(new)
        if m > best_n:
            best, best_n = [set(s) for s in new], m
            consider(m, _edges(new))
        if m >= n - 2 or rng.random() < 0.15:
            cur = new
        if len(cur) < best_n - 6:
            cur = [set(s) for s in best]


# ----------------------------------------------------------------------------
# Driver. Usable budget T = 0.8 * time_limit.
#   A  degree-thinned dense structured graph (W(q) or PG(2,q)), repeated
#   B  slack structured graph (or Haar) grown and saturated
#   C  LNS from the best valid graph until the end
# Every kept graph passes lib.is_valid. The Haar fallback is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.8 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))
    if not lib.is_valid(fallback[0], fallback[1], d, D):
        fallback = (2, [(0, 1)])
    best_n, best_e = fallback
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if best_n >= moore:
        return best_n, list(best_e)

    big_q, small_q = _choose_q(d, D)

    # Phase A: thinned dense structured graph, repeated with fresh randomness.
    if big_q is not None:
        base = _structured(D, big_q)
        already_ok = all(len(s) <= d for s in base)
        while time.monotonic() < at(0.45):
            adj, alive = _reduce(base, d, rng)
            res = _repair(adj, alive, D, rng, at(0.45))
            if res is None:
                break
            new = _complete(res, d, D, at(0.45), rng)
            consider(len(new), _edges(new))
            if already_ok or best_n >= moore:
                break

    if best_n >= moore:
        return best_n, list(best_e)

    # Phase B: slack structured base (or Haar), grown and saturated.
    if small_q is not None:
        start_adj = _structured(D, small_q)
    else:
        start_adj = _to_adj(fallback[0], fallback[1])
    new = _complete(start_adj, d, D, at(0.55), rng)
    consider(len(new), _edges(new))

    if best_n >= moore:
        return best_n, list(best_e)

    # Phase C: LNS from the best valid graph found so far.
    if time.monotonic() < at(1.0):
        _lns(_to_adj(best_n, best_e), d, D, at(1.0), rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
