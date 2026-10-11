import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (carried over from the parent).
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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (parent's search family).
# ----------------------------------------------------------------------------

_PENALTY = 1000


def _sample_group(target, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order near target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, target // k2)
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _cost(k, G, D, darts, perms):
    """Unreached (representative, vertex) pairs plus duplicate-dart penalties. Zero means valid."""
    seen = set()
    dup = 0
    for i, j, s in darts:
        key = (i, j, s)
        if key in seen:
            dup += 1
        seen.add(key)
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen_v = [False] * N
        seen_v[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen_v[v]:
                        seen_v[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total + _PENALTY * dup


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _search(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over the voltages of a base with k vertices per side.

    Each of the d layers is a permutation of range(k), so every vertex has degree d
    (before duplicate darts are removed). Returns (n, edges) with diameter <= D, or None.
    """
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, p[i], rng.randrange(G)] for p in layers for i in range(k)]
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_pm = perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = [mul(g, new_s) for g in range(G)]
        c2 = _cost(k, G, D, darts, perms)
        temp = 2.0 * (1.0 - t / iters) + 0.05
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            darts[idx][2] = old_s
            perms[idx] = old_pm

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# NEW: greedy spare-slot augmentation.
#
# After duplicate darts are removed (or for a baseline like PG(2,q), which has
# spare degree when d > q + 1), some vertices have degree < d. A new vertex v
# can join a set S of spare vertices on one side, provided every existing vertex
# is within distance D of v. Since dist(v, w) = 1 + min_{s in S} dist(s, w), this
# holds iff the radius-(D-1) balls around S cover all existing vertices. We pick
# S greedily as a set cover (at most d members), and add v only when the cover is
# complete. Adding a vertex never increases any existing distance, so earlier
# valid pairs stay valid, and bipartiteness is kept since v sits on the opposite
# side of every neighbour.
# ----------------------------------------------------------------------------

def _two_color(n, adj):
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


def _ball_masks(n, adj, R):
    """Bitmask per vertex of all vertices within distance R."""
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


def _augment(n, edges, d, D, deadline, rng, max_tries=300):
    """Greedily attach new vertices to spare degree slots while diameter <= D holds."""
    edges = list(edges)
    for _ in range(max_tries):
        if time.monotonic() > deadline:
            break
        adj = [[] for _ in range(n)]
        deg = [0] * n
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
            deg[u] += 1
            deg[v] += 1
        spare = [v for v in range(n) if deg[v] < d]
        if not spare:
            break
        color = _two_color(n, adj)
        masks = _ball_masks(n, adj, D - 1)
        full = (1 << n) - 1
        sides = [0, 1]
        rng.shuffle(sides)
        added = False
        for side in sides:
            avail = {s for s in spare if color[s] == side}
            if not avail:
                continue
            cov = 0
            chosen = []
            while len(chosen) < d and cov != full and avail:
                best_s, best_g = None, 0
                for s in avail:
                    g = (masks[s] & ~cov).bit_count()
                    if g > best_g:
                        best_g, best_s = g, s
                if best_s is None:
                    break
                chosen.append(best_s)
                cov |= masks[best_s]
                avail.discard(best_s)
            if cov == full and chosen:
                v = n
                n += 1
                for s in chosen:
                    edges.append((v, s))
                added = True
                break
        if not added:
            break
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
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

    def consider_augmented(n, e):
        consider(n, e)
        if time.monotonic() < deadline:
            n2, e2 = _augment(n, e, d, D, deadline, rng)
            consider(n2, e2)

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            if D == 3 and lib.is_prime_power(d - 1):
                consider(pg[0], pg[1])
                return best
            consider_augmented(pg[0], pg[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                consider(gq[0], gq[1])
                return best
            consider_augmented(gq[0], gq[1])

    # Main search: bi-Cayley lifts with 1-4 base vertices per side, then augment.
    while time.monotonic() < deadline:
        k = rng.choice([1, 2, 2, 3, 4])
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        order, mul = g
        res = _search(d, D, k, order, mul, rng, deadline, 1200)
        if res is not None:
            consider_augmented(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
