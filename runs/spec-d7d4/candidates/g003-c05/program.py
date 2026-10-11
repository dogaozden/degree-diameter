import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions: projective plane (D = 3) and generalized quadrangle W(q) (D >= 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (capped for build speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Cover-based vertex extension and edge saturation (diameter-preserving growth).
# ----------------------------------------------------------------------------

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


def _extend_cover(n, edges, d, D, deadline, rng):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    attempts_max = 300

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(attempts_max):
                if time.monotonic() >= deadline:
                    break
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


def _saturate_edges(n, edges, d, rng):
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
    """Cover vertices first, then saturate with spare degree. Both preserve diameter."""
    cur_n, cur_e = n, list(edges)
    for _ in range(20):
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
# Cyclic Haar graph search (new bold family for D >= 4).
# Haar graph H(m, S): a_i ~ b_j iff j - i in S (mod m), |S| = k, 0 in S WLOG.
# The group Z_m is transitive on each side, so the diameter is <= D exactly when
# every a-vertex and every b-vertex is within distance D of a_0 and b_0.
# The cost below counts the unreached vertices from those two sources.
# ----------------------------------------------------------------------------

def _haar_unreached(m, S, D):
    total = 0
    for src in (0, m):
        seen = [False] * (2 * m)
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for x in frontier:
                if x < m:
                    for s in S:
                        y = m + (x + s) % m
                        if not seen[y]:
                            seen[y] = True
                            nxt.append(y)
                else:
                    j = x - m
                    for s in S:
                        y = (j - s) % m
                        if not seen[y]:
                            seen[y] = True
                            nxt.append(y)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * m - count
    return total


def _haar_anneal(m, k, D, rng, deadline, iters):
    """Simulated annealing over the shift set S (|S| = k, 0 in S). Returns S with zero cost, else None."""
    S = [0] + rng.sample(range(1, m), k - 1)
    c = _haar_unreached(m, S, D)
    T0, T1 = 5.0, 0.5
    for it in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        i = rng.randrange(1, k)
        new = rng.randrange(1, m)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = _haar_unreached(m, S, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
        else:
            S[i] = old
    return S if c == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    span = deadline - start

    def at(f):
        return start + f * span

    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # D = 3: projective plane, grown by cover extension.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, at(0.5), rng)
            consider(n2, e2)
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    if D >= 4 and d >= 3:
        # Generalized quadrangle W(q) with cover growth (short phase).
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, at(0.2), rng)
            consider(n2, e2)

        # Phase A: cyclic Haar graphs of full degree d, searched from just above the
        # current best order upward. Each success raises the bar.
        hi = sum((d - 1) ** i for i in range(D))  # Moore-type bound on m
        m = best_n // 2 + 1
        while m <= hi and time.monotonic() < at(0.6):
            S = _haar_anneal(m, d, D, rng, at(0.6), 800)
            if S is not None:
                n, e = lib.haar_graph(m, S)
                consider(n, e)
            m += 1

        # Phase B: cyclic Haar graphs of degree d - 1 (one spare degree per vertex),
        # then cover growth using the spare degree.
        k = d - 1
        if k >= 3:
            hi_k = sum((k - 1) ** i for i in range(D))
            m = max(k + 1, hi_k - 60)
            while m <= hi_k and time.monotonic() < deadline:
                S = _haar_anneal(m, k, D, rng, deadline, 800)
                if S is not None:
                    n, e = lib.haar_graph(m, S)
                    grow_until = min(deadline, time.monotonic() + 3.0)
                    n2, e2 = _grow(n, e, d, D, grow_until, rng)
                    consider(n2, e2)
                    consider(n, e)
                m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
