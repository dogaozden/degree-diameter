import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graph: incidence graph of the generalized quadrangle W(q) (diameter 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q); points 0..P-1, lines P..2P-1."""
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
    lines = []
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
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _largest_pp(limit):
    for q in range(limit, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


# ----------------------------------------------------------------------------
# Bitmask distance utilities.
# ----------------------------------------------------------------------------

def _radius_balls(adj, n, r):
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        nb = list(ball)
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb[v] = x
        ball = nb
    return ball


def _bad(adj, n, D):
    """Number of unordered pairs at distance > D (unreachable counts)."""
    ball = _radius_balls(adj, n, D)
    return sum(n - b.bit_count() for b in ball) // 2


# ----------------------------------------------------------------------------
# Lossless growth: a new vertex covered by <= d opposite-side vertices.
# ----------------------------------------------------------------------------

def _greedy(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains)
        if best_g == 0:
            break
        if randomize and rng.random() < 0.5:
            opts = [i for i, g in enumerate(gains) if g >= best_g - 1 and g > 0]
        else:
            opts = [i for i, g in enumerate(gains) if g == best_g]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _try_cover(adj, color, d, D, rng):
    n = len(adj)
    if D < 2:
        return None
    ball = _radius_balls(adj, n, D - 1)
    full = (1 << n) - 1
    sides = [0, 1]
    rng.shuffle(sides)
    for c in sides:
        cands = [s for s in range(n) if color[s] == c and len(adj[s]) < d]
        if not cands:
            continue
        for attempt in range(8):
            chosen = _greedy(cands, ball, full, d, rng, attempt > 0)
            if chosen:
                return 1 - c, chosen
    return None


def _add_vertex(adj, color, c, chosen):
    v = len(adj)
    adj.append([])
    color.append(c)
    for s in chosen:
        adj[s].append(v)
        adj[v].append(s)


def _saturate(adj, color, d, rng):
    """Add edges between non-adjacent opposite-side vertices with spare degree."""
    n = len(adj)
    L = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    R = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in L for b in R]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].append(b)
            adj[b].append(a)


# ----------------------------------------------------------------------------
# Annealing on a fixed vertex set: moves are add-edge, endpoint-move,
# and degree-preserving double-edge swap. Cost = bad pairs.
# ----------------------------------------------------------------------------

def _rand_vertex(adj, color, side, rng):
    n = len(adj)
    for _ in range(20):
        v = rng.randrange(n)
        if adj[v] and (side is None or color[v] == side):
            return v
    return None


def _propose(adj, color, d, rng):
    n = len(adj)
    r = rng.random()
    if r < 0.30:
        L = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
        R = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
        if not L or not R:
            return None
        for _ in range(4):
            a = rng.choice(L)
            b = rng.choice(R)
            if b not in adj[a]:
                return [(1, a, b)]
        return None
    if r < 0.65:
        v = _rand_vertex(adj, color, None, rng)
        if v is None:
            return None
        b = rng.choice(adj[v])
        cv = color[v]
        X = [x for x in range(n)
             if color[x] == cv and x != v and len(adj[x]) < d and x not in adj[b]]
        if not X:
            return None
        x = rng.choice(X)
        return [(0, v, b), (1, x, b)]
    v = _rand_vertex(adj, color, 0, rng)
    c = _rand_vertex(adj, color, 0, rng)
    if v is None or c is None or v == c:
        return None
    b = rng.choice(adj[v])
    e = rng.choice(adj[c])
    if b == e or e in adj[v] or b in adj[c]:
        return None
    return [(0, v, b), (0, c, e), (1, v, e), (1, c, b)]


def _apply(adj, ops):
    for kind, u, v in ops:
        if kind:
            adj[u].append(v)
            adj[v].append(u)
        else:
            adj[u].remove(v)
            adj[v].remove(u)


def _undo(ops):
    return [(1 - k, u, v) for k, u, v in reversed(ops)]


def _anneal(adj, color, d, D, rng, deadline, T0=1.0, T1=0.05):
    n = len(adj)
    cost = _bad(adj, n, D)
    if cost == 0:
        return 0
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - start) / span)
        ops = _propose(adj, color, d, rng)
        if ops is None:
            continue
        _apply(adj, ops)
        c2 = _bad(adj, n, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _apply(adj, _undo(ops))
    return cost


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    t0 = time.monotonic()
    total = max(0.5, 0.8 * time_limit - 1.0)
    deadline = t0 + total
    rng = random.Random(seed)

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    best = fallback if lib.is_valid(fallback[0], fallback[1], d, D) else (1, [])

    def record(adj_, color_):
        nonlocal best
        n_ = len(adj_)
        if n_ <= best[0]:
            return
        e_ = [(u, v) for u in range(n_) for v in adj_[u] if u < v]
        if lib.is_valid(n_, e_, d, D):
            best = (n_, e_)

    base = None
    try:
        if D == 3:
            q = _largest_pp(d - 1)
            if q:
                base = lib.projective_plane_incidence(q)
        elif D == 4:
            q = _largest_pp(d - 1)
            if q:
                base = _gq_w(q)
    except Exception:
        base = None
    if base is None:
        base = fallback

    try:
        n0, e0 = base
        m0 = n0 // 2
        es = {(min(u, v), max(u, v)) for u, v in e0}
        adj = [[] for _ in range(n0)]
        for u, v in es:
            adj[u].append(v)
            adj[v].append(u)
        color = [0] * m0 + [1] * m0
        if not lib.is_valid(n0, list(es), d, D):
            raise ValueError("base invalid")

        _saturate(adj, color, d, rng)
        record(adj, color)
        moore = lib._moore_bound(d, D)

        while time.monotonic() < deadline:
            if len(adj) >= moore:
                break
            got = _try_cover(adj, color, d, D, rng)
            if got is not None:
                c, chosen = got
                _add_vertex(adj, color, c, chosen)
                _saturate(adj, color, d, rng)
                record(adj, color)
                continue

            adj2 = [list(a) for a in adj]
            color2 = list(color)
            cnt0 = color.count(0)
            cnt1 = len(color) - cnt0
            c_new = 0 if cnt0 <= cnt1 else 1
            adj2.append([])
            color2.append(c_new)

            now = time.monotonic()
            remaining = deadline - now
            slice_end = now + max(0.5, min(remaining, 0.12 * total))
            cost = _anneal(adj2, color2, d, D, rng, min(deadline, slice_end))
            if cost == 0:
                adj, color = adj2, color2
                _saturate(adj, color, d, rng)
                record(adj, color)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
