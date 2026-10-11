import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases: projective planes (D = 3) and generalized quadrangles W(q) (D = 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, girth 8."""
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


def _structured_base(d, D):
    """Largest structured base for the given (d, D), or None."""
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                return lib.projective_plane_incidence(q)
    elif D == 4:
        for q in range(min(d - 1, 9), 1, -1):
            if lib.is_prime_power(q):
                return _gq_w(q)
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


def _bad_count(n, adj, D):
    """Number of unordered vertex pairs at distance > D (bitmask balls)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nb = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb.append(x)
        ball = nb
    return sum(n - b.bit_count() for b in ball) // 2


# ----------------------------------------------------------------------------
# Growth by vertex insertion followed by degree-preserving 2-switch annealing.
# A new vertex is attached to d opposite-side vertices (dropping an edge where a
# target is full). Bipartite 2-switches keep degrees and sides fixed while the
# number of pairs at distance > D is driven to zero.
# ----------------------------------------------------------------------------

def _add_vertex(n, edges, color, d, rng):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    c = rng.randrange(2)
    targets = [t for t in range(n) if color[t] != c]
    rng.shuffle(targets)
    targets.sort(key=lambda t: deg[t] >= d)
    targets = targets[:d]
    edges = list(edges)
    v = n
    for t in targets:
        if deg[t] >= d:
            idx = [k for k, (x, y) in enumerate(edges) if x == t or y == t]
            k = rng.choice(idx)
            x, y = edges[k]
            edges[k] = edges[-1]
            edges.pop()
            deg[x] -= 1
            deg[y] -= 1
        edges.append((t, v))
        deg[t] += 1
    return n + 1, edges, list(color) + [c]


def _switch_anneal(n, edges, color, d, D, deadline, rng):
    """Anneal over bipartite 2-switches until diameter <= D. Returns edges or None."""
    adj = [set() for _ in range(n)]
    E = []
    for u, v in edges:
        a, b = (u, v) if color[u] == 0 else (v, u)
        E.append([a, b])
        adj[a].add(b)
        adj[b].add(a)
    left = [v for v in range(n) if color[v] == 0]
    right = [v for v in range(n) if color[v] == 1]

    def saturate():
        spL = [v for v in left if len(adj[v]) < d]
        spR = [v for v in right if len(adj[v]) < d]
        if not spL or not spR:
            return
        pairs = [(a, b) for a in spL for b in spR if b not in adj[a]]
        rng.shuffle(pairs)
        for a, b in pairs:
            if len(adj[a]) < d and len(adj[b]) < d:
                adj[a].add(b)
                adj[b].add(a)
                E.append([a, b])

    saturate()
    cost = _bad_count(n, adj, D)
    if cost == 0:
        return [(a, b) for a, b in E]
    if len(E) < 2:
        return None

    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = 2.0 * (0.01 ** ((now - start) / span))
        if rng.random() < 0.02:
            before = len(E)
            saturate()
            if len(E) != before:
                cost = _bad_count(n, adj, D)
            continue
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _bad_count(n, adj, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            E[i] = [a, e]
            E[j] = [c, b]
            cost = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return [(a, b) for a, b in E]


def _grow(n, edges, d, D, deadline, rng):
    """Repeatedly insert a vertex and repair by switch annealing; returns the last valid graph."""
    cur_n, cur_e = n, list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 5:
        remaining = deadline - time.monotonic()
        slice_end = time.monotonic() + min(remaining, max(1.5, 0.15 * remaining))
        color = _bipartition(cur_n, _adjacency(cur_n, cur_e))
        n2, e2, col2 = _add_vertex(cur_n, cur_e, color, d, rng)
        res = _switch_anneal(n2, e2, col2, d, D, min(slice_end, deadline), rng)
        if res is None:
            fails += 1
        else:
            cur_n, cur_e = n2, res
            fails = 0
    return cur_n, cur_e


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

    # Safe fallback: K_{d,d} has diameter 2 (valid for D >= 2).
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2 or best[0] >= lib._moore_bound(d, D):
        return best

    bases = []
    sb = _structured_base(d, D)
    if sb is not None and lib.is_valid(sb[0], sb[1], d, D):
        bases.append(sb)
        consider(sb[0], sb[1])
    if not bases:
        bases = [best]

    # Restart loop: alternate between growing the best graph and growing a fresh base.
    attempt = 0
    while time.monotonic() < deadline - 0.5:
        if best[0] > 0 and rng.random() < 0.5:
            src = best
        else:
            src = bases[attempt % len(bases)]
        attempt += 1
        n2, e2 = _grow(src[0], src[1], d, D, deadline, rng)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
        if not lib.is_valid(best[0], best[1], d, D):
            best = (1, [])
    return best
