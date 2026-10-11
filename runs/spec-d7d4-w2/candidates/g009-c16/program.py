import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs: projective planes (D = 3) and generalized quadrangles W(q) (D >= 4).
# ----------------------------------------------------------------------------

def _best_pg(d, count=1):
    """Incidence graphs of PG(2, q) for the largest prime powers q with q + 1 <= d."""
    out = []
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            out.append(lib.projective_plane_incidence(q))
            if len(out) == count:
                break
    return out


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
# Graph utilities.
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


def _balls_radius(n, adj, r):
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


def _bad(n, adj, D):
    return sum(n - b.bit_count() for b in _balls_radius(n, adj, D)) // 2


# ----------------------------------------------------------------------------
# NEW: pair growth.
#
# Add two adjacent vertices a (colour 0) and b (colour 1). a is joined to a set
# S1 of colour-1 vertices, b to a set S0 of colour-0 vertices. Every existing x
# is within D of a and of b iff
#   (A) x in Ball_{D-1}(S1) or x in Ball_{D-2}(S0), and
#   (B) x in Ball_{D-1}(S0) or x in Ball_{D-2}(S1).
# Existing distances can only shrink, so the diameter bound is preserved.
# A single vertex cannot use this: it has to cover with one radius only.
# ----------------------------------------------------------------------------

def _pair_grow(n, edges, d, D, rng, randomize):
    if D < 3 or n == 0:
        return None
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    B1 = _balls_radius(n, adj, D - 1)
    B2 = _balls_radius(n, adj, D - 2)
    full = (1 << n) - 1
    cA = 0
    cB = 0
    cap = d - 1
    pool1 = [s for s in range(n) if color[s] == 1 and deg[s] < d]
    pool0 = [s for s in range(n) if color[s] == 0 and deg[s] < d]
    chosen1, chosen0 = [], []

    while (cA != full or cB != full) and (len(chosen1) < cap or len(chosen0) < cap):
        cand = []
        if len(chosen1) < cap:
            for s in pool1:
                g = (B1[s] & ~cA).bit_count() + (B2[s] & ~cB).bit_count()
                if g > 0:
                    cand.append((g, 1, s))
        if len(chosen0) < cap:
            for s in pool0:
                g = (B2[s] & ~cA).bit_count() + (B1[s] & ~cB).bit_count()
                if g > 0:
                    cand.append((g, 0, s))
        if not cand:
            break
        top = max(c[0] for c in cand)
        slack = 1 if (randomize and rng.random() < 0.3) else 0
        opts = [c for c in cand if c[0] >= top - slack]
        g, side, s = rng.choice(opts) if randomize else opts[0]
        if side == 1:
            chosen1.append(s)
            pool1.remove(s)
            cA |= B1[s]
            cB |= B2[s]
        else:
            chosen0.append(s)
            pool0.remove(s)
            cA |= B2[s]
            cB |= B1[s]

    if cA != full or cB != full or not chosen1 or not chosen0:
        return None
    a, b = n, n + 1
    new = list(edges)
    new.append((a, b))
    for s in chosen1:
        new.append((s, a))
    for s in chosen0:
        new.append((s, b))
    return n + 2, new


def _pair_expand(n, edges, d, D, deadline, rng):
    """Repeat pair growth, falling back to single cover vertices; saturate at the end."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        r = None
        for attempt in range(12):
            r = _pair_grow(cur_n, cur_e, d, D, rng, attempt > 0)
            if r:
                break
        if r is None:
            r = _add_one(cur_n, cur_e, d, D, rng)
        if r is None:
            break
        cur_n, cur_e = r
    cur_e = _saturate_edges(cur_n, cur_e, d, rng)
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Cover helpers.
# ----------------------------------------------------------------------------

def _greedy_cover(cands, ball, full, d, rng, randomize):
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


def _saturate_edges(n, edges, d, rng):
    """Add random edges between non-adjacent opposite-side vertices with spare degree."""
    edges = list(edges)
    adj = _adjacency(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _remove_vertex(n, edges, x):
    """Delete vertex x; the last vertex takes its label. Returns (n-1, edges)."""
    last = n - 1

    def m(v):
        return x if v == last else v

    new = [(m(u), m(v)) for u, v in edges if u != x and v != x]
    return n - 1, new


def _add_one(n, edges, d, D, rng):
    """Add one vertex by a degree-respecting cover; return (n+1, edges) or None."""
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    ball = _balls_radius(n, adj, D - 1)
    full = (1 << n) - 1
    sides = [0, 1]
    rng.shuffle(sides)
    for c in sides:
        cands = [s for s in range(n) if color[s] == c and deg[s] < d]
        if not cands:
            continue
        chosen = None
        for attempt in range(30):
            chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
            if chosen:
                break
        if chosen:
            v = n
            new_edges = list(edges)
            for s in chosen:
                new_edges.append((s, v))
            return n + 1, new_edges
    return None


def _fill(n, edges, d, D, rng, deadline):
    """Repeatedly add cover vertices while possible, then saturate spare slots."""
    while time.monotonic() < deadline:
        r = _add_one(n, edges, d, D, rng)
        if r is None:
            break
        n, edges = r
    edges = _saturate_edges(n, edges, d, rng)
    return n, edges


# ----------------------------------------------------------------------------
# Local search: vertex removal with refill, and pair-growth refill.
# ----------------------------------------------------------------------------

def _drop_refill(n, edges, d, D, rng, deadline, tries=8):
    """Remove the vertex (among a few samples) leaving fewest bad pairs, then refill."""
    best = None
    for _ in range(tries):
        if time.monotonic() >= deadline:
            break
        x = rng.randrange(n)
        n2, e2 = _remove_vertex(n, edges, x)
        b = _bad(n2, _adjacency(n2, e2), D)
        if best is None or b < best[0]:
            best = (b, n2, e2)
    if best is None:
        return None
    _, n2, e2 = best
    return _fill(n2, e2, d, D, rng, deadline)


def _random_move(n, edges, d, D, rng, deadline):
    """Remove a random vertex, repair the diameter if cheaply possible, then refill."""
    x = rng.randrange(n)
    rn, re = _remove_vertex(n, edges, x)
    if rn <= 1:
        return None
    if not lib.within_diameter(rn, re, D):
        re = _saturate_edges(rn, re, d, rng)
        if not lib.within_diameter(rn, re, D):
            return None
    # Alternate refill: pair growth first, then single covers.
    for _ in range(4):
        if time.monotonic() >= deadline:
            break
        r = _pair_grow(rn, re, d, D, rng, True)
        if r is None:
            break
        rn, re = r
    return _fill(rn, re, d, D, rng, deadline)


def _search(d, D, deadline, rng, box):
    """Local search with plateau moves. box[0] holds the best verified (n, edges)."""
    cn, ce = box[0]
    stale = 0
    while time.monotonic() < deadline:
        if stale > 150:
            cn, ce = box[0]
            stale = 0
        if rng.random() < 0.5:
            cand = _drop_refill(cn, ce, d, D, rng, deadline)
        else:
            cand = _random_move(cn, ce, d, D, rng, deadline)
        if cand is None:
            stale += 1
            continue
        rn, re = cand
        if not lib.within_diameter(rn, re, D):
            stale += 1
            continue
        if rn > box[0][0] and lib.is_valid(rn, re, d, D):
            box[0] = (rn, re)
            cn, ce = rn, re
            stale = 0
        elif rn >= cn:
            cn, ce = rn, re
            stale += 1
        else:
            stale += 1


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    expand_deadline = start + 0.45 * T
    search_deadline = start + 0.82 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best
    if d == 2:
        cyc = [(i, (i + 1) % (2 * D)) for i in range(2 * D)]
        consider(2 * D, cyc)
        return best

    if best[0] >= lib.moore_bound(d, D):
        return best

    bases = []
    if D == 3:
        bases = _best_pg(d, 2)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                bases.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
    else:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            if time.monotonic() >= expand_deadline:
                break
            try:
                bases.append(_gq_w(q))
            except Exception:
                pass

    for b in bases:
        consider(b[0], b[1])

    # Pair-growth expansion from saturated bases, with randomized restarts.
    rot = 0
    while bases and time.monotonic() < expand_deadline:
        src = bases[rot % len(bases)]
        rot += 1
        try:
            n0, e0 = src[0], _saturate_edges(src[0], src[1], d, rng)
            n2, e2 = _pair_expand(n0, e0, d, D, expand_deadline, rng)
            consider(n2, e2)
        except Exception:
            break

    # Local search on the best graph found.
    if best[0] >= lib.moore_bound(d, D):
        return best
    if time.monotonic() < search_deadline and best[0] >= 2:
        box = [best]
        try:
            _search(d, D, search_deadline, rng, box)
        except Exception:
            pass
        if box[0][0] > best[0] and lib.is_valid(box[0][0], box[0][1], d, D):
            best = box[0]

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
