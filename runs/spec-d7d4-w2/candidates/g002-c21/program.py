import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: projective plane (D = 3) and generalized quadrangle W(q) (D >= 4).
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


# ----------------------------------------------------------------------------
# Shared helpers.
# ----------------------------------------------------------------------------

def _adj_of(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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
    """Pick at most d candidates whose radius balls cover the full bitmask, or None."""
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
    """Join deficient opposite-side vertices. Adding edges never breaks the diameter."""
    edges = list(edges)
    adj = _adj_of(n, edges)
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


# ----------------------------------------------------------------------------
# NEW: adjacent pair extension.
#
# Add two vertices a (side 0) and w (side 1) joined by the edge a-w.
#   * a is joined to a set S on side 1 whose radius-(D-1) balls cover the old graph.
#   * w is joined to a set T on side 0 whose radius-(D-1) balls cover the old graph.
# Then a reaches every old vertex within D (via S), w reaches every old vertex
# within D (via T), a and w are adjacent, and old pairs keep their distances.
# Both new vertices use at most d-1 cover edges, and the pair adds two vertices
# in one step. The parent only adds single vertices.
# ----------------------------------------------------------------------------

def _pair_extend(n, edges, d, D, rng, restarts):
    if D < 2 or d < 2 or n < 2:
        return None
    adj = _adj_of(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    full = (1 << n) - 1
    ball = _balls_radius(n, adj, D - 1)
    side0 = [s for s in range(n) if color[s] == 0 and deg[s] < d]
    side1 = [s for s in range(n) if color[s] == 1 and deg[s] < d]
    if not side0 or not side1:
        return None
    for attempt in range(restarts):
        rnd = attempt > 0
        S = _greedy_cover(side1, ball, full, d - 1, rng, rnd)
        if S is None:
            continue
        T = _greedy_cover(side0, ball, full, d - 1, rng, rnd)
        if T is None:
            continue
        a, w = n, n + 1
        E = list(edges)
        E.append((a, w))
        for s in S:
            E.append((s, a))
        for t in T:
            E.append((t, w))
        return n + 2, E
    return None


def _pair_chain(n, edges, d, D, rng, deadline, restarts):
    """Repeat pair extension and edge saturation while covers still exist."""
    while time.monotonic() < deadline:
        res = _pair_extend(n, edges, d, D, rng, restarts)
        if res is None:
            break
        n, edges = res
        edges = _saturate_edges(n, edges, d, rng)
    return n, edges


# ----------------------------------------------------------------------------
# Twin augmentation by packing.
# ----------------------------------------------------------------------------

def _twin_packing(n, adj, slack, rng, deadline):
    """Annealed kick-out local search for a large set of candidates whose twins fit."""
    cand = [x for x in range(n) if adj[x] and all(slack[w] > 0 for w in adj[x])]
    if not cand:
        return []
    inset = [False] * n
    load = [0] * n
    size = 0

    def remove(x):
        nonlocal size
        inset[x] = False
        size -= 1
        for w in adj[x]:
            load[w] -= 1

    def insert(x):
        nonlocal size
        inset[x] = True
        size += 1
        for w in adj[x]:
            load[w] += 1

    def try_insert(c):
        kicked = []
        for w in adj[c]:
            while load[w] >= slack[w]:
                opts = [x for x in adj[w] if inset[x]]
                x = rng.choice(opts)
                remove(x)
                kicked.append(x)
        insert(c)
        return kicked

    start = time.monotonic()
    span = max(1e-9, deadline - start)

    order = cand[:]
    rng.shuffle(order)
    for c in order:
        if not inset[c] and all(load[w] < slack[w] for w in adj[c]):
            insert(c)
    best = [x for x in cand if inset[x]]
    best_size = size

    it = 0
    T = 0.5
    while True:
        it += 1
        if (it & 127) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = (now - start) / span
            T = 0.05 + 0.5 * (1.0 - frac)
        c = rng.choice(cand)
        if inset[c]:
            continue
        kicked = try_insert(c)
        delta = 1 - len(kicked)
        if delta >= 0 or rng.random() < math.exp(delta / T):
            if size > best_size:
                best_size = size
                best = [x for x in cand if inset[x]]
        else:
            remove(c)
            for x in kicked:
                insert(x)
    return best


def _twin_augment(n, edges, d, rng, deadline):
    """Add twins of a packed vertex set. Bipartite and diameter-preserving."""
    adj = _adj_of(n, edges)
    slack = [max(0, d - len(a)) for a in adj]
    chosen = _twin_packing(n, adj, slack, rng, deadline)
    E = list(edges)
    N = n
    for x in chosen:
        for w in adj[x]:
            E.append((N, w))
        N += 1
    return N, E


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.80 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n:
            try:
                ok = lib.is_valid(n, e, d, D)
            except Exception:
                ok = False
            if ok:
                best = (n, e)
                best_n = n

    try:
        if D == 2:
            return best

        if D == 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                while time.monotonic() < deadline:
                    n2, e2 = _pair_chain(pg[0], pg[1], d, D, rng, deadline, 40)
                    consider(n2, e2)
                    break
            return best

        # D >= 4: generalized quadrangle bases plus twin and pair extensions.
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        bases = []
        for q in qs:
            if time.monotonic() >= deadline:
                break
            gq = _gq_w(q)
            consider(gq[0], gq[1])
            bases.append(gq)

        while time.monotonic() < deadline and bases:
            base = rng.choice(bases)
            if rng.random() < 0.5:
                n2, e2 = _pair_chain(base[0], base[1], d, D, rng, deadline, 30)
            else:
                tn, te = _twin_augment(base[0], base[1], d, rng,
                                       min(deadline, time.monotonic() + 0.15 * time_limit))
                consider(tn, te)
                n2, e2 = _pair_chain(tn, te, d, D, rng, deadline, 30)
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
