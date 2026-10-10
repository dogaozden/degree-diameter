import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _pg_candidates(d, count):
    """Prime powers q with q + 1 <= d, largest first (at most `count` of them)."""
    qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
    return qs[:count]


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
# New construction: greedy spare-degree extension.
#
# A graph whose vertices have degree < d can be grown. A new vertex x of colour c
# is joined to at most d spare vertices of the opposite colour. Adding x only
# shortens old distances, so the sole requirement is that x reaches every old
# vertex within D. That holds iff every old vertex lies within distance D-1 of a
# chosen neighbour, which is a set-cover problem. We solve it greedily on bitmask
# balls of radius D-1 and verify the result by construction.
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _two_colour(n, adj):
    """Proper 2-colouring of a bipartite graph (BFS per component)."""
    color = [-1] * n
    for s in range(n):
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
    return color


def _radius_balls(n, adj, R):
    """Bitmask of all vertices within distance R of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return reach


def _extend(n, edges, d, D, rng, deadline, tries=4, max_fails=3):
    """Greedy spare-degree extension. Returns (n, edges), possibly enlarged.

    Every edge stays bipartite (new vertex takes the colour opposite its
    neighbours) and no vertex exceeds degree d. Diameter is preserved by the
    coverage argument above.
    """
    edges = list(edges)
    if n == 0 or D < 2:
        return n, edges
    adj = _adjacency(n, edges)
    if all(len(a) >= d for a in adj):
        return n, edges
    color = _two_colour(n, adj)
    fails = 0
    while fails < max_fails and time.monotonic() < deadline:
        balls = _radius_balls(n, adj, D - 1)
        full = (1 << n) - 1
        placed = False
        colours = [0, 1]
        rng.shuffle(colours)
        for c in colours:
            cand0 = [b for b in range(n) if color[b] == 1 - c and len(adj[b]) < d]
            if not cand0:
                continue
            for _ in range(tries):
                pool = cand0[:]
                rng.shuffle(pool)
                covered = 0
                chosen = []
                while len(chosen) < d and covered != full:
                    best = -1
                    best_gain = 0
                    for b in pool:
                        g = (balls[b] & ~covered).bit_count()
                        if g > best_gain:
                            best, best_gain = b, g
                    if best < 0:
                        break
                    chosen.append(best)
                    covered |= balls[best]
                    pool.remove(best)
                if covered == full and chosen:
                    x = n
                    n += 1
                    adj.append([])
                    color.append(c)
                    for b in chosen:
                        edges.append((b, x))
                        adj[b].append(x)
                        adj[x].append(b)
                    placed = True
                    break
            if placed:
                break
        fails = 0 if placed else fails + 1
    return n, edges


# ----------------------------------------------------------------------------
# Annealed bi-Cayley voltage lifts over semidirect products (from the parent).
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
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


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments.

    Each layer is a permutation of range(k), so every vertex has degree exactly d.
    Returns (n, edges) with diameter <= D, or None.
    """
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
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

    # Projective-plane incidence graphs (diameter 3) with spare degree extended greedily.
    # Spare degree d - (q + 1) is the resource the extension consumes.
    if D >= 3:
        for q in _pg_candidates(d, 3):
            if time.monotonic() > deadline:
                break
            n0, e0 = lib.projective_plane_incidence(q)
            consider(n0, e0)
            n1, e1 = _extend(n0, e0, d, D, rng, deadline)
            consider(n1, e1)

    # Generalized quadrangle W(q) (diameter 4) with the same extension.
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            n0, e0 = gq
            consider(n0, e0)
            n1, e1 = _extend(n0, e0, d, D, rng, deadline)
            consider(n1, e1)

    # Main search. A fraction of attempts build a lift of degree d-1, which leaves
    # one spare slot per vertex, and then extend it greedily to degree d.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        use_deficit = d >= 3 and rng.random() < 0.3
        dd = d - 1 if use_deficit else d
        if use_deficit:
            target = int(best_n * rng.uniform(0.5, 0.9))
        else:
            target = best_n
        base = target // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(dd, D, k, order, mul, rng, deadline, iters=400)
        if res is None:
            continue
        n1, e1 = res
        if use_deficit:
            n1, e1 = _extend(n1, e1, d, D, rng, deadline)
        consider(n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
