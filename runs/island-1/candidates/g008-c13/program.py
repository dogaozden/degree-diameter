import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Araujo-Pardo–López family for D = 3 (record for d = q + 2).
# ----------------------------------------------------------------------------

def _largest_pp_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _araujo_candidate(d):
    q = _largest_pp_le(d - 2)
    if q is None or q < 3:
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except Exception:
        return None


# ----------------------------------------------------------------------------
# Diameter-preserving slack filling (adds bipartite edges between spare vertices).
# ----------------------------------------------------------------------------

def _fill_slack(n, edges, d, seed):
    adjs = [set() for _ in range(n)]
    for u, v in edges:
        adjs[u].add(v)
        adjs[v].add(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adjs[u]:
                if color[w] == -1:
                    color[w] = 1 - color[u]
                    stack.append(w)
    deg = [len(a) for a in adjs]
    rng = random.Random(seed)
    out = list(edges)
    for _ in range(4):
        A = [v for v in range(n) if color[v] == 0 and deg[v] < d]
        B = [v for v in range(n) if color[v] == 1 and deg[v] < d]
        rng.shuffle(A)
        rng.shuffle(B)
        added = False
        for a in A:
            for b in B:
                if deg[a] >= d:
                    break
                if deg[b] < d and b not in adjs[a]:
                    adjs[a].add(b)
                    adjs[b].add(a)
                    deg[a] += 1
                    deg[b] += 1
                    out.append((a, b))
                    added = True
        if not added:
            break
    return n, out


# ----------------------------------------------------------------------------
# Shared helpers for the cover-based growth and the rewiring search.
#
# A new vertex x on one side is joined to d spare vertices c_1..c_k on the other
# side. dist(x, v) <= D iff some c_i has dist(c_i, v) <= D - 1, so we pick the
# neighbours greedily to cover every existing vertex by radius-(D-1) balls.
# ----------------------------------------------------------------------------

def _greedy_cover(cands, reach, full, d, rng):
    """Pick up to d candidates whose balls cover the bitmask full; return list or None."""
    pool = list(cands)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while len(chosen) < d and covered != full:
        best = None
        best_gain = 0
        for c in pool:
            g = (reach[c] & ~covered).bit_count()
            if g > best_gain:
                best, best_gain = c, g
        if best is None:
            break
        chosen.append(best)
        covered |= reach[best]
        pool = [c for c in pool if c != best]
    if covered & full == full:
        return chosen
    return None


def _reach(adj, R):
    """Bitmask per vertex of all vertices within distance R."""
    N = len(adj)
    reach = [1 << v for v in range(N)]
    for _ in range(R):
        nxt = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return reach


def _two_color(adj):
    """Return a 2-colouring list, or None if the graph is not bipartite."""
    N = len(adj)
    color = [-1] * N
    for s in range(N):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if color[w] == -1:
                    color[w] = 1 - color[u]
                    stack.append(w)
                elif color[w] == color[u]:
                    return None
    return color


def _valid_adj(adj, d, D):
    N = len(adj)
    edges = [(u, v) for u in range(N) for v in adj[u] if u < v]
    return lib.is_valid(N, edges, d, D)


# ----------------------------------------------------------------------------
# NEW: iterated grow-and-rewire local search ("rewire to free slack, then grow").
#
# Growth: attach a new vertex by greedy radius-(D-1) cover. This never breaks
# the diameter bound, so growth steps are always valid.
# Rewiring: detach a random vertex, re-attach it by a fresh greedy cover on its
# own side, and keep the move only if the whole graph is still valid. Accepted
# rewires random-walk over valid graphs, which can free degree slots so that
# later growth steps succeed.
# ----------------------------------------------------------------------------

def _grow_once(adj, color, d, R, rng):
    """Try to add one new vertex with a greedy cover; mutates adj and color."""
    N = len(adj)
    full = (1 << N) - 1
    reach = _reach(adj, R)
    sides = [0, 1]
    rng.shuffle(sides)
    for opp in sides:
        cands = [c for c in range(N) if color[c] == opp and len(adj[c]) < d]
        if not cands:
            continue
        chosen = _greedy_cover(cands, reach, full, d, rng)
        if chosen:
            x = N
            adj.append(set(chosen))
            color.append(1 - opp)
            for c in chosen:
                adj[c].add(x)
            return True
    return False


def _rewire(adj, color, d, D, rng):
    """Detach a random vertex and re-attach it by a fresh cover; keep only if valid."""
    N = len(adj)
    x = rng.randrange(N)
    if not adj[x]:
        return False
    R = D - 1
    old = list(adj[x])
    for c in old:
        adj[c].discard(x)
    adj[x] = set()
    reach = _reach(adj, R)
    full = ((1 << N) - 1) & ~(1 << x)
    opp = 1 - color[x]
    cands = [c for c in range(N) if color[c] == opp and c != x and len(adj[c]) < d]
    chosen = _greedy_cover(cands, reach, full, d, rng) if cands else None
    ok = False
    if chosen:
        for c in chosen:
            adj[c].add(x)
            adj[x].add(c)
        ok = _valid_adj(adj, d, D)
    if not ok:
        for c in list(adj[x]):
            adj[c].discard(x)
        adj[x] = set()
        for c in old:
            adj[c].add(x)
            adj[x].add(c)
    return ok


def _ils(n, edges, d, D, seed, deadline):
    """Grow-and-rewire local search starting from a valid graph; returns a valid graph."""
    if D < 2 or n == 0:
        return n, list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    if any(len(a) > d for a in adj):
        return n, list(edges)
    color = _two_color(adj)
    if color is None or not lib.is_valid(n, list(edges), d, D):
        return n, list(edges)
    rng = random.Random(seed)
    R = D - 1
    while time.monotonic() < deadline:
        if _grow_once(adj, color, d, R, rng):
            continue
        for _ in range(4):
            if time.monotonic() >= deadline:
                break
            _rewire(adj, color, d, D, rng)
    N = len(adj)
    return N, [(u, v) for u in range(N) for v in adj[u] if u < v]


# ----------------------------------------------------------------------------
# Group-voltage lifts over semidirect products, with a fast two-stage evaluator.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _search(d, D, k, G, rng, iters, deadline):
    """Simulated annealing over voltages in a group of order G. Returns (n, edges) or None."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    G = order
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = []
    for p in layers:
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    best_cost = cost
    best_darts = [list(x) for x in darts]
    best_perms = list(perms)

    T0 = 3.0
    for t in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.05
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_perm = perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = _right_perm(mul, G, new_s)
        c2 = _cost(k, G, D, darts, perms)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_darts = [list(x) for x in darts]
                best_perms = list(perms)
        else:
            darts[idx][2] = old_s
            perms[idx] = old_perm

    if best_cost == 0:
        return _edges(k, G, best_darts, best_perms)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Base constructions.
    bases = []
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            bases.append(pg)
        al = _araujo_candidate(d)
        if al is not None:
            n_al, e_al = al
            bases.append(_fill_slack(n_al, e_al, d, seed))
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            bases.append(gq)

    for b in bases:
        consider(b[0], b[1])

    # NEW: grow-and-rewire local search from the best valid graph so far.
    ils_end = start + 0.45 * (deadline - start)
    if D >= 2 and time.monotonic() < ils_end:
        n1, e1 = _ils(best_n, best[1], d, D, seed, ils_end)
        consider(n1, e1)

    # Main search: annealed group voltage lifts with 1-3 base vertices per side.
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
        res = _search(d, D, k, G, rng, 1500, deadline)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
