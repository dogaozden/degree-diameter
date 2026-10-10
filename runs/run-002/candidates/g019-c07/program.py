import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from parent).
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
# Group-voltage lifts over semidirect products (parent family, kept as a
# search option for the parent phase).
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
    """Simulated annealing over voltages in a group of order G."""
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
# NEW construction: annealed edge-switching search on d-regular bipartite
# graphs with a fixed number of vertices per side.
#
# Start from a random d-regular bipartite graph on a + a vertices. A move
# swaps two edges (i1,j1),(i2,j2) -> (i1,j2),(i2,j1), which keeps the graph
# bipartite and d-regular. The cost is the number of ordered vertex pairs at
# distance greater than D (unreachable pairs included), computed with big-int
# bitsets. Simulated annealing accepts uphill moves early on. A ratchet on a
# grows the side size after each success and shrinks it after each failure.
# ----------------------------------------------------------------------------

def _cost_bip(N, adj, D):
    """Number of ordered vertex pairs not within distance D (0 means valid)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        changed = False
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
            if r != reach[v]:
                changed = True
        reach = new
        if not changed:
            break
    return sum(N - r.bit_count() for r in reach)


def _random_regular_bip(a, d, rng):
    """Adjacency sets for a d-regular bipartite graph with a vertices per side, or None."""
    if d > a:
        return None
    adjL = [set() for _ in range(a)]
    for _ in range(d):
        perm = list(range(a))
        rng.shuffle(perm)
        ok = False
        for _ in range(2000):
            bad = [i for i in range(a) if perm[i] in adjL[i]]
            if not bad:
                ok = True
                break
            for i in bad:
                j = rng.randrange(a)
                perm[i], perm[j] = perm[j], perm[i]
        if not ok:
            return None
        for i in range(a):
            adjL[i].add(perm[i])
    return adjL


def _bip_anneal(a, d, D, rng, deadline):
    """Try to find a d-regular bipartite graph on a+a vertices with diameter <= D.

    Returns a list of edges (i, j) with left index i and right index j, or None.
    """
    adjL = _random_regular_bip(a, d, rng)
    if adjL is None:
        return None
    edges = [(i, j) for i in range(a) for j in adjL[i]]
    N = 2 * a

    def build_adj():
        adj = [[] for _ in range(N)]
        for i, j in edges:
            adj[i].append(a + j)
            adj[a + j].append(i)
        return adj

    cost = _cost_bip(N, build_adj(), D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    m = len(edges)
    while cost > 0:
        now = time.monotonic()
        if now > deadline:
            return None
        frac = (now - t0) / span
        T = 2.0 * (1.0 - frac) + 0.2

        e1 = rng.randrange(m)
        e2 = rng.randrange(m)
        i1, j1 = edges[e1]
        i2, j2 = edges[e2]
        if i1 == i2 or j1 == j2 or j2 in adjL[i1] or j1 in adjL[i2]:
            continue

        adjL[i1].discard(j1)
        adjL[i2].discard(j2)
        adjL[i1].add(j2)
        adjL[i2].add(j1)
        edges[e1] = (i1, j2)
        edges[e2] = (i2, j1)

        new = _cost_bip(N, build_adj(), D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
        else:
            adjL[i1].discard(j2)
            adjL[i2].discard(j1)
            adjL[i1].add(j1)
            adjL[i2].add(j2)
            edges[e1] = (i1, j1)
            edges[e2] = (i2, j2)

    return edges


def _alt_phase(d, D, best_n, rng, deadline):
    """Ratchet the side size a of the switching search. Returns (n, edges) or None."""
    best = None
    a = max(2, best_n // 2)
    while time.monotonic() < deadline - 0.2:
        remaining = deadline - time.monotonic()
        slice_end = min(deadline, time.monotonic() + max(2.0, remaining * 0.25))
        res = _bip_anneal(a, d, D, rng, slice_end)
        if res is not None:
            best = (2 * a, [(i, a + j) for i, j in res])
            a += max(1, a // 80)
        else:
            a = max(2, a - max(1, a // 150))
    return best


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Parent phase gets a share of the budget; the new search gets the rest.
    use_alt = d >= 3 and D >= 3
    parent_deadline = start + (0.4 * budget if use_alt else budget)

    while time.monotonic() < parent_deadline:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
        res = _search(d, D, k, G, rng, 1500, parent_deadline)
        if res is not None:
            consider(res[0], res[1])

    # New phase: edge-switching annealing on d-regular bipartite graphs.
    if use_alt and time.monotonic() < deadline - 0.5:
        alt = _alt_phase(d, D, best_n, rng, deadline)
        if alt is not None:
            consider(alt[0], alt[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


def build(d, D, seed, time_limit):
    try:
        return _build(d, D, seed, time_limit)
    except Exception:
        if d < 1 or D < 1:
            return 1, []
        if D == 1:
            return 2, [(0, 1)]
        return lib.haar_graph(d, range(d))
