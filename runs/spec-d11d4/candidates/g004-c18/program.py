import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions: projective plane (D = 3) and generalized quadrangle W(q) (D = 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q); bipartite, diameter 4."""
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (capped at 9 for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Cover-based vertex extension (diameter-preserving growth).
# ----------------------------------------------------------------------------

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
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
    """Greedy set cover of `full` by at most d candidate balls; None if it fails."""
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


def _cover_ls(cands, ball, full, d, rng, steps, deadline):
    """Swap-based local search for a cover of `full` by k = min(d, |cands|) candidate balls."""
    if not cands:
        return None
    k = min(d, len(cands))
    S = rng.sample(cands, k)
    in_s = set(S)

    def union(sel):
        u = 0
        for s in sel:
            u |= ball[s]
        return u

    cost = (full & ~union(S)).bit_count()
    for step in range(steps):
        if cost == 0:
            break
        if (step & 255) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        rest = S[:i] + S[i + 1:]
        miss = full & ~union(rest)
        best_t, best_g = None, -1
        for t in rng.sample(cands, min(30, len(cands))):
            if t in in_s:
                continue
            g = (ball[t] & miss).bit_count()
            if g > best_g:
                best_t, best_g = t, g
        if best_t is None:
            continue
        newcost = (miss & ~ball[best_t]).bit_count()
        if newcost <= cost or rng.random() < 0.02:
            in_s.discard(S[i])
            S[i] = best_t
            in_s.add(best_t)
            cost = newcost
    return S if cost == 0 else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover everything within distance D-1 of the graph."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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
            for attempt in range(25):
                if time.monotonic() >= deadline:
                    break
                if attempt < 5:
                    chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                else:
                    chosen = _cover_ls(cands, ball, full, d, rng, 2000, deadline)
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
    """Greedily join deficient opposite-side vertices in random order (keeps bipartiteness)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
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


def _grow(n, edges, d, D, deadline, rng):
    """Alternate cover-vertex extension with saturation of leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Bold branch: rewire-and-regrow. Remove a few random edges to free degree slots,
# regrow with cover extension, and keep the result only if it is strictly larger
# and passes the exact validity check.
# ----------------------------------------------------------------------------

def _rewire_regrow(n, edges, d, D, deadline, rng):
    best_n, best_e = n, list(edges)
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        e = list(cur_e)
        # Remove a small random set of edges to create spare degree.
        kill = rng.randint(1, 3)
        for _ in range(kill):
            if not e:
                break
            e.pop(rng.randrange(len(e)))
        sub_deadline = min(deadline, time.monotonic() + 3.0)
        n2, e2 = _extend_cover(cur_n, e, d, D, sub_deadline, rng)
        e2 = _saturate_edges(n2, e2, d, rng)
        if n2 >= best_n and lib.is_valid(n2, e2, d, D):
            if n2 > best_n:
                best_n, best_e = n2, list(e2)
            cur_n, cur_e = n2, e2
    return best_n, best_e


# ----------------------------------------------------------------------------
# Driver. Every candidate is checked with lib.is_valid before it can be kept.
# ----------------------------------------------------------------------------

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
            return True
        return False

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.4 * time_limit, rng)
            consider(n2, e2)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            # Stage 1: iterated cover growth from the base, stacking extensions.
            grow_deadline = start + 0.35 * time_limit
            cur_n, cur_e = gq[0], gq[1]
            t = 0
            while time.monotonic() < grow_deadline and t < 40:
                n2, e2 = _grow(cur_n, cur_e, d, D, grow_deadline,
                               random.Random(seed * 131 + t))
                if n2 > cur_n and lib.is_valid(n2, e2, d, D):
                    cur_n, cur_e = n2, e2
                consider(n2, e2)
                t += 1

            # Stage 2 (bold): rewire-and-regrow from the best graph so far.
            if time.monotonic() < deadline:
                rn, re_ = _rewire_regrow(best_n, best[1], d, D, deadline, rng)
                consider(rn, re_)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
