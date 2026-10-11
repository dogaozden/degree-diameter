import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs: projective plane (D = 3) and generalized quadrangle W(q) (D >= 4).
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
    """W(q) for the largest prime power q with q + 1 <= d (q capped for build speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers.
# ----------------------------------------------------------------------------

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


def _saturate_edges(n, edges, d, rng):
    """Add edges between spare-degree vertices on opposite sides. Adding edges never breaks diameter."""
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


def _cover_search(ball, cands, full, d, rng, budget):
    """Find <= d candidates whose radius balls cover `full`; return list or None."""
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
        free = [s for s in cands if s not in used]
        gains = {s: (ball[s] & rem).bit_count() for s in free}
        best = max(gains.values(), default=0)
        if best == 0 or rem.bit_count() > best * (d - depth):
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
            opts = [s for s in free if gains[s] and (ball[s] >> w) & 1]
            if best_opts is None or len(opts) < len(best_opts):
                best_opts = opts
        if not best_opts:
            return False
        rng.shuffle(best_opts)
        best_opts.sort(key=lambda s: -gains[s])
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


def _grow_exact(n, edges, d, D, deadline, rng, budget):
    """Repeatedly add a vertex whose neighbourhood covers every existing vertex within D-1."""
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
        placed = False
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [s for s in range(n) if color[s] == 1 - c and deg[s] < d]
            if not cands:
                continue
            chosen = _cover_search(ball, cands, full, d, rng, budget)
            if chosen:
                v = n
                n += 1
                color.append(c)
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


# ----------------------------------------------------------------------------
# NEW: twin augmentation.
#
# A twin v' of a vertex v (same side, identical neighbour set N(v)) keeps every
# distance between old vertices unchanged and sits at distance 2 from v, so the
# diameter stays <= D. Making a twin of v costs one spare degree on each vertex
# of N(v). So choosing which vertices to twin is a set packing: candidate c uses
# one unit of capacity from each neighbour, and each neighbour w has capacity
# d - deg(w). In a generalized quadrangle with d = q+2 this is exactly:
#   - twin a set of pairwise non-collinear points (partial ovoid), and
#   - twin a set of pairwise disjoint lines (partial spread, up to q^2+1 lines),
# and the two packings use different spare degrees, so they are independent.
# Packing is found by randomized 1-swap local search, plus a small exact-cover
# DFS that can hit a perfect packing (a full spread) when every capacity is 1.
# ----------------------------------------------------------------------------

def _packing_ls(cands, adj, cap, rng, deadline, iters):
    """Randomized 1-swap local search for a large packing of candidates with capacity cap[w]."""
    order = list(cands)
    rng.shuffle(order)
    use = {}
    users = {}
    chosen = set()

    def add(c):
        chosen.add(c)
        for w in adj[c]:
            use[w] = use.get(w, 0) + 1
            users.setdefault(w, set()).add(c)

    def remove(c):
        chosen.discard(c)
        for w in adj[c]:
            use[w] -= 1
            users[w].discard(c)

    for c in order:
        if all(use.get(w, 0) < cap[w] for w in adj[c]):
            add(c)
    best = set(chosen)
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        c = order[rng.randrange(len(order))]
        if c in chosen:
            if rng.random() < 0.002:
                remove(c)
            continue
        conflicts = set()
        for w in adj[c]:
            if use.get(w, 0) >= cap[w]:
                conflicts.update(users[w])
        if not conflicts:
            add(c)
        elif len(conflicts) == 1:
            remove(next(iter(conflicts)))
            add(c)
        else:
            continue
        if len(chosen) > len(best):
            best = set(chosen)
    return list(best)


def _exact_cover(cands, adj, universe, rng, deadline, budget):
    """Choose candidates whose neighbourhoods partition `universe` exactly; None on failure."""
    by_w = {w: [] for w in universe}
    for c in cands:
        for w in adj[c]:
            by_w[w].append(c)
    uncovered = set(universe)
    chosen = []
    nodes = [0]

    def ok(c):
        return all(w in uncovered for w in adj[c])

    def rec():
        if not uncovered:
            return True
        nodes[0] += 1
        if nodes[0] > budget or ((nodes[0] & 31) == 0 and time.monotonic() > deadline):
            return False
        best = None
        for w in uncovered:
            opts = [c for c in by_w[w] if ok(c)]
            if best is None or len(opts) < len(best):
                best = opts
                if len(best) <= 1:
                    break
        if not best:
            return False
        rng.shuffle(best)
        for c in best:
            removed = list(adj[c])
            uncovered.difference_update(removed)
            chosen.append(c)
            if rec():
                return True
            chosen.pop()
            uncovered.update(removed)
        return False

    return list(chosen) if rec() else None


def _twin_augment(n, edges, d, rng, deadline):
    """Add twin vertices by packing, then saturate leftover spare degree. Returns (n, edges)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)
    cap = [d - len(adj[v]) for v in range(n)]
    new_edges = []
    cur_n = n
    for side in (0, 1):
        cands = [c for c in range(n)
                 if color[c] == side and adj[c] and all(cap[w] >= 1 for w in adj[c])]
        if not cands:
            continue
        best = []
        for _ in range(3):
            if time.monotonic() > deadline:
                break
            sol = _packing_ls(cands, adj, cap, rng, deadline, 40000)
            if len(sol) > len(best):
                best = sol
        universe = {w for c in cands for w in adj[c]}
        if time.monotonic() < deadline and all(cap[w] == 1 for w in universe):
            ec = _exact_cover(cands, adj, universe, rng, deadline, 400)
            if ec and len(ec) > len(best):
                best = ec
        for c in best:
            v = cur_n
            cur_n += 1
            for w in adj[c]:
                new_edges.append((w, v))
    e2 = _saturate_edges(cur_n, list(edges) + new_edges, d, rng)
    return cur_n, e2


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    base = _best_pg(d) if D == 3 else (_best_gq(d) if D >= 4 else None)
    if base is not None:
        consider(*base)
        bn, be = base

        # New idea: twin packing (partial ovoid + partial spread on the quadrangle).
        aug = _twin_augment(bn, be, d, rng, start + 0.2 * time_limit)
        consider(*aug)

        # Exact-cover growth from the fresh base, from the twin-augmented graph,
        # and from the best graph after another twin pass.
        grow_end = start + 0.8 * time_limit
        attempt = 0
        while time.monotonic() < grow_end:
            arng = random.Random(seed * 1000003 + attempt)
            phase = attempt % 3
            if phase == 0:
                sn, se = bn, be
            elif phase == 1:
                sn, se = aug
            else:
                sn, se = _twin_augment(best[0], best[1], d, arng, grow_end)
            n2, e2 = _grow_exact(sn, se, d, D, grow_end, arng, 1500)
            e2 = _saturate_edges(n2, e2, d, arng)
            consider(n2, e2)
            attempt += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
