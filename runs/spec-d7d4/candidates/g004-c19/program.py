import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs.
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _gq_base(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _pg_base(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Graph helpers.
# ----------------------------------------------------------------------------

def _adj(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _balls(n, adj, r):
    """Bitmask of all vertices within distance r of each vertex."""
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


def _colour(n, adj):
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


# ----------------------------------------------------------------------------
# NEW helper: load-aware exact cover.
#
# A new vertex v on side c is valid iff its neighbour set S (other side, spare
# degree left) has every existing vertex within distance D-1 of some s in S.
# This depth-limited search finds such S of size <= d. Among candidates with the
# same gain, it prefers the least-loaded vertex (lowest current degree), so spare
# degree stays spread out and later vertices still find cover candidates.
# ----------------------------------------------------------------------------

def _cover_search(ball, cands, full, d, rng, budget, deg):
    used = set()
    chosen = []
    nodes = [0]

    def rec(covered, depth):
        if covered == full:
            return True
        if depth >= d or nodes[0] >= budget:
            return False
        nodes[0] += 1
        rem = full & ~covered
        gains = {}
        for s in cands:
            if s in used:
                continue
            g = (ball[s] & rem).bit_count()
            if g:
                gains[s] = g
        if not gains:
            return False
        best = max(gains.values())
        if rem.bit_count() > best * (d - depth):
            return False
        bits = []
        x = rem
        while x:
            low = x & -x
            bits.append(low.bit_length() - 1)
            x ^= low
        sample = rng.sample(bits, min(6, len(bits)))
        best_opts = None
        for w in sample:
            opts = [s for s in gains if (ball[s] >> w) & 1]
            if best_opts is None or len(opts) < len(best_opts):
                best_opts = opts
        if not best_opts:
            return False
        rng.shuffle(best_opts)
        best_opts.sort(key=lambda s: (-gains[s], deg[s]))
        for s in best_opts:
            used.add(s)
            chosen.append(s)
            if rec(covered | ball[s], depth + 1):
                return True
            used.discard(s)
            chosen.pop()
            if nodes[0] >= budget:
                break
        return False

    return list(chosen) if rec(0, 0) else None


def _grow(n, edges, d, D, deadline, rng, budget):
    """Repeatedly add a vertex whose neighbourhood covers the graph within D-1."""
    edges = list(edges)
    adj = _adj(n, edges)
    deg = [len(a) for a in adj]
    col = _colour(n, adj)
    while time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        placed = False
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [s for s in range(n) if col[s] == 1 - c and deg[s] < d]
            if not cands:
                continue
            chosen = _cover_search(ball, cands, full, d, rng, budget, deg)
            if chosen:
                v = n
                n += 1
                col.append(c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                placed = True
                break
        if not placed:
            break
    return n, edges


def _saturate(n, edges, d, rng):
    """Add cross-side edges between vertices with spare degree; distances only shrink."""
    edges = list(edges)
    adj = _adj(n, edges)
    deg = [len(a) for a in adj]
    col = _colour(n, adj)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    left = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if col[v] == 1 and deg[v] < d]
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
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    if D == 3:
        base = _pg_base(d)
        if base is not None:
            consider(base[0], base[1])
            n2, e2 = _grow(base[0], base[1], d, D, start + 0.4 * time_limit, rng, 400)
            consider(n2, _saturate(n2, e2, d, rng))

    if D >= 4:
        base = _gq_base(d)
        if base is not None:
            base_n, base_e = base
            consider(base_n, base_e)
            attempt = 0
            while time.monotonic() < deadline:
                arng = random.Random(seed * 1000003 + attempt)
                n2, e2 = _grow(base_n, base_e, d, D, deadline, arng, 1500)
                consider(n2, _saturate(n2, e2, d, arng))
                attempt += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
