import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases (used for the grow phase, which provides the safe baseline).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _best_gq(d):
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q capped for speed)."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Graph helpers.
# ----------------------------------------------------------------------------

def _adj_lists(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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


def _cost(n, edges, D):
    """Number of ordered pairs at distance more than D (0 means diameter <= D)."""
    adj = _adj_lists(n, edges)
    balls = _balls(n, adj, D)
    return sum(n - b.bit_count() for b in balls)


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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices. Returns list or None."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        bg = max(gains, default=0)
        if bg == 0:
            break
        thr = bg - 1 if (randomize and rng.random() < 0.5) else bg
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover all vertices within radius D-1."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = _adj_lists(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
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


def _saturate(n, edges, d, rng):
    """Join deficient opposite-side vertices in random order (only shrinks distances)."""
    edges = list(edges)
    adj = _adj_lists(n, edges)
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
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _duplicate_twins(n, edges, d, rng):
    """Add non-adjacent twins while neighbours have spare degree (keeps distances and bipartiteness)."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


# ----------------------------------------------------------------------------
# NEW construction: voltage lifts over small non-abelian groups.
# A base multigraph with k vertices per side (each vertex of degree d) is lifted
# over a group G of order g, giving 2*k*g vertices. The voltages are found by
# hill climbing on the number of vertex pairs farther apart than D.
# ----------------------------------------------------------------------------

def _groups(g):
    """Cyclic group Z_g and all semidirect products Z_m x| Z_k with m*k = g. List of (order, mul)."""
    order, mul, _ = lib.cyclic_group(g)
    out = [(order, mul)]
    for k in range(2, g):
        if g % k:
            continue
        m = g // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
                continue
            order, mul, _ = lib.semidirect_group(m, k, r)
            out.append((order, mul))
    return out


def _mult_matrix(k, d, rng):
    """k x k nonnegative integer matrix with all row and column sums equal to d."""
    M = [[0] * k for _ in range(k)]
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            M[i][perm[i]] += 1
    return M


def _climb(k, d, D, order, mul, rng, steps, deadline):
    """Hill-climb voltages for a fixed group until the lift has diameter <= D. Returns (n, edges) or None."""
    M = _mult_matrix(k, d, rng)
    pairs = [(i, j) for i in range(k) for j in range(k) if M[i][j] > 0]
    V = {p: rng.sample(range(order), M[p[0]][p[1]]) for p in pairs}

    def build():
        darts = [(i, k + j, s) for (i, j) in pairs for s in V[(i, j)]]
        return lib.group_lift(2 * k, darts, order, mul)

    n, e = build()
    cur = _cost(n, e, D)
    for _ in range(steps):
        if cur == 0:
            return n, e
        if time.monotonic() >= deadline:
            break
        p = rng.choice(pairs)
        idx = rng.randrange(len(V[p]))
        s = rng.randrange(order)
        if s in V[p]:
            continue
        old = V[p][idx]
        V[p][idx] = s
        n2, e2 = build()
        c2 = _cost(n2, e2, D)
        if c2 <= cur or rng.random() < 0.01:
            cur, n, e = c2, n2, e2
        else:
            V[p][idx] = old
    if cur == 0:
        return n, e
    return None


def _lift_search(d, D, best_n, deadline, rng, moore):
    """Upward search over (k, g): find the smallest lift order above the current best. Returns (n, edges) or None."""
    ks = (1, 2, 3)
    bestn = best_n
    best = None
    cur = {k: bestn // (2 * k) + 1 for k in ks}
    cache = {}
    while time.monotonic() < deadline:
        live = []
        for k in ks:
            g = max(cur[k], bestn // (2 * k) + 1, d)
            if 2 * k * g <= moore:
                live.append(k)
        if not live:
            break
        for k in live:
            now = time.monotonic()
            if now >= deadline:
                break
            g = max(cur[k], bestn // (2 * k) + 1, d)
            cur[k] = g
            if 2 * k * g > moore:
                continue
            if g not in cache:
                cache[g] = _groups(g)
            groups = cache[g]
            slice_end = min(deadline, now + 4.0)
            found = None
            while time.monotonic() < slice_end and found is None:
                order, mul = rng.choice(groups)
                found = _climb(k, d, D, order, mul, rng, 400, slice_end)
            if found is not None:
                bestn, best = found[0], found
                cur[k] = bestn // (2 * k) + 1
            else:
                cur[k] = g + 1
    return best


# ----------------------------------------------------------------------------
# Driver.
#   Phase 1 (to 30% of usable budget): structured base (W(q) or PG(2,q)) grown with
#           optional twin duplication. This is the safe baseline.
#   Phase 2 (to 92%): voltage-lift search over Z_g and semidirect groups, k = 1..3.
#   The best candidate that passes lib.is_valid is returned; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase 1: structured base, grown.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            end = at(0.30)
            while time.monotonic() < end:
                n, e = n0, list(e0)
                if rng.random() < 0.5:
                    n, e = _duplicate_twins(n, e, d, rng)
                e = _saturate(n, e, d, rng)
                n, e = _grow(n, e, d, D, end, rng)
                consider(n, e)

    # Phase 2: voltage lifts over small groups (new construction).
    if D >= 3 and d >= 3 and time.monotonic() < at(0.92):
        moore = lib.moore_bound(d, D)
        res = _lift_search(d, D, best_n, at(0.92), rng, moore)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
