import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: generalized quadrangle W(q) (diameter 4) and projective plane (diameter 3).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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


# ----------------------------------------------------------------------------
# Graph helpers.
# ----------------------------------------------------------------------------

def _adj(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _colors(n, adj):
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
    """ball[v] = bitmask of vertices within distance r of v."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        nb = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb.append(x)
        ball = nb
    return ball


def _remove(n, edges, x):
    """Delete vertex x; the last vertex takes its label."""
    last = n - 1

    def m(v):
        return x if v == last else v

    return n - 1, [(m(u), m(v)) for u, v in edges if u != x and v != x]


def _saturate(n, edges, d, rng):
    """Add edges between opposite-side vertices with spare degree (never breaks diameter)."""
    edges = list(edges)
    deg = [0] * n
    ex = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        ex.add((min(u, v), max(u, v)))
    color = _colors(n, _adj(n, edges))
    L = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    R = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    if not L or not R:
        return edges
    pairs = [(a, b) for a in L for b in R if (min(a, b), max(a, b)) not in ex]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# Cover-based vertex addition. A new vertex on side 1-c is joined to a set S of
# side-c vertices with |S| <= d whose radius-(D-1) balls cover all vertices.
# Then every vertex is within distance D of the new one, and old distances
# only shrink, so validity is preserved.
# ----------------------------------------------------------------------------

def _cover(cands, ball, full, room, budget):
    """Branch-and-bound exact cover of `full` by at most `room` candidate balls."""
    nodes = [0]

    def rec(covered, chosen, left):
        unc = full & ~covered
        if not unc:
            return chosen
        if left == 0:
            return None
        nodes[0] += 1
        if nodes[0] > budget:
            return None
        gains = {s: (ball[s] & unc).bit_count() for s in cands}
        mx = max(gains.values())
        if mx == 0 or unc.bit_count() > left * mx:
            return None
        w = (unc & -unc).bit_length() - 1
        opts = [s for s in cands if gains[s] > 0 and (ball[s] >> w) & 1]
        opts.sort(key=lambda s: -gains[s])
        for s in opts:
            r = rec(covered | ball[s], chosen + [s], left - 1)
            if r is not None:
                return r
            if nodes[0] > budget:
                return None
        return None

    return rec(0, [], room)


def _greedy(cands, ball, full, room, rng):
    unc = full
    chosen = []
    pool = list(cands)
    rng.shuffle(pool)
    while unc and len(chosen) < room and pool:
        best, bg = None, 0
        for s in pool:
            g = (ball[s] & unc).bit_count()
            if g > bg or (g == bg and g > 0 and rng.random() < 0.3):
                best, bg = s, g
        if best is None:
            break
        chosen.append(best)
        unc &= ~ball[best]
        pool.remove(best)
    return chosen if unc == 0 else None


def _add_vertex(n, edges, d, D, rng):
    adj = _adj(n, edges)
    deg = [len(a) for a in adj]
    color = _colors(n, adj)
    ball = _balls(n, adj, D - 1)
    full = (1 << n) - 1
    sides = [0, 1]
    rng.shuffle(sides)
    for c in sides:
        cands = [s for s in range(n) if color[s] == c and deg[s] < d]
        if not cands:
            continue
        chosen = _cover(cands, ball, full, d, 1500)
        if chosen is None:
            for _ in range(20):
                chosen = _greedy(cands, ball, full, d, rng)
                if chosen:
                    break
        if chosen:
            v = n
            ne = list(edges) + [(s, v) for s in chosen]
            return n + 1, ne
    return None


def _grow(n, edges, d, D, deadline, rng):
    while time.monotonic() < deadline:
        r = _add_vertex(n, edges, d, D, rng)
        if r is None:
            break
        n, edges = r
        edges = _saturate(n, edges, d, rng)
    return n, edges


# ----------------------------------------------------------------------------
# Iterated local search: kick (delete 1-2 vertices), repair by saturation,
# keep only if still valid, then regrow with cover vertices.
# ----------------------------------------------------------------------------

def _ils(n, edges, d, D, deadline, rng):
    best = (n, list(edges))
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        if cur_n < best[0] - 6:
            cur_n, cur_e = best[0], list(best[1])
        kn, ke = cur_n, cur_e
        k = 1 if rng.random() < 0.7 else 2
        for _ in range(k):
            if kn <= 2:
                break
            kn, ke = _remove(kn, ke, rng.randrange(kn))
        ke = _saturate(kn, ke, d, rng)
        if not lib.within_diameter(kn, ke, D):
            continue
        kn, ke = _grow(kn, ke, d, D, deadline, rng)
        if kn > best[0] and lib.is_valid(kn, ke, d, D):
            best = (kn, list(ke))
        if kn >= cur_n or (kn == cur_n - 1 and rng.random() < 0.1):
            cur_n, cur_e = kn, ke
    return best


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _prime_powers_desc(limit, lo=2):
    return [q for q in range(limit, lo - 1, -1) if lib.is_prime_power(q)]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, Moore-optimal for D = 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback
    try:
        if D == 2:
            return best

        def consider(n, e):
            nonlocal best
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)

        # Bases with q + 1 <= d.
        bases = []
        if D == 3:
            for q in _prime_powers_desc(min(d - 1, 23))[:2]:
                bases.append(lib.projective_plane_incidence(q))
        else:
            for q in _prime_powers_desc(min(d - 1, 7))[:2]:
                bases.append(_gq_w(q))

        for b in bases:
            consider(b[0], b[1])

        if not bases:
            return best

        # Split the remaining time evenly across bases, leaving a margin.
        for i, (bn, be) in enumerate(bases):
            now = time.monotonic()
            if now >= deadline:
                break
            slice_end = now + (deadline - now) / (len(bases) - i)
            slice_end = min(slice_end, deadline)
            if lib.within_diameter(bn, be, D):
                grown_n, grown_e = _grow(bn, be, d, D, slice_end, rng)
                grown_e = _saturate(grown_n, grown_e, d, rng)
                consider(grown_n, grown_e)
                res = _ils(grown_n, grown_e, d, D, slice_end, rng)
                consider(res[0], res[1])

        if not lib.is_valid(best[0], best[1], d, D):
            return fallback
        return best
    except Exception:
        return fallback
