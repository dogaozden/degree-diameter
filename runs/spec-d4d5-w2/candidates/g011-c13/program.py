import itertools
import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Classical bases: projective plane and generalized quadrangle W(q).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New family: bi-regular permutation lifts searched directly on the graph.
#
# Blocks A_0..A_{k-1} and B_0..B_{k-1}, each of size m. A block pair (i, j)
# carries M[i][j] permutations of Z-indices; each permutation p gives edges
# A_i[x] -- B_j[p[x]]. Row and column sums of M equal d, so every vertex has
# degree d. Within a block pair the permutations must be pointwise distinct,
# which keeps the graph simple. Bipartiteness is automatic. The search is
# simulated annealing over swaps inside single permutations, with the cost
# being the number of ordered (vertex, unreached vertex) pairs at distance > D.
# ----------------------------------------------------------------------------

def _block_configs(d):
    """Block-count matrices M with all row and column sums equal to d."""
    cfgs = [(1, [[d]])]
    if d >= 2:
        for a in range(1, d // 2 + 1):
            cfgs.append((2, [[a, d - a], [d - a, a]]))
    return cfgs


def _lift_candidates(d, floor_n, moore):
    """(n, k, M, m) candidates with floor_n < n <= min(moore, floor_n + 60), sorted by n."""
    out = []
    nmax = min(moore, floor_n + 60)
    for k, M in _block_configs(d):
        step = 2 * k
        m0 = floor_n // step + 1
        for m in range(m0, nmax // step + 1):
            n = step * m
            if floor_n < n <= nmax:
                out.append((n, k, M, m))
    out.sort(key=lambda c: c[0])
    return out


def _pcost(n, adj, D):
    """Sum over vertices of the number of vertices not reached within distance D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _perm_anneal(d, D, k, m, M, rng, deadline):
    """Anneal permutation lifts of the block configuration (k, M) with block size m."""
    n = 2 * k * m

    def A(i, x):
        return i * m + x

    def B(j, y):
        return k * m + j * m + y

    darts = []  # each entry: [i, j, p] with p a list of length m
    for i in range(k):
        for j in range(k):
            t = M[i][j]
            if t == 0:
                continue
            for s in rng.sample(range(m), t):
                darts.append([i, j, [(x + s) % m for x in range(m)]])

    adj = [[] for _ in range(n)]
    for i, j, p in darts:
        for x in range(m):
            a, b = A(i, x), B(j, p[x])
            adj[a].append(b)
            adj[b].append(a)

    sib = [[b for b in range(len(darts))
            if b != a and darts[b][0] == darts[a][0] and darts[b][1] == darts[a][1]]
           for a in range(len(darts))]

    cost = _pcost(n, adj, D)
    T0, T_end = 5.0, 0.2
    start_t = time.monotonic()
    span = max(1e-3, deadline - start_t)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - start_t) / span)
        T = T0 * (T_end / T0) ** frac

        a = rng.randrange(len(darts))
        i, j, p = darts[a]
        x, y = rng.sample(range(m), 2)
        px, py = p[x], p[y]
        ok = True
        for b in sib[a]:
            q = darts[b][2]
            if q[x] == py or q[y] == px:
                ok = False
                break
        if not ok:
            continue

        ax, ay = A(i, x), A(i, y)
        bx_old, by_old = B(j, px), B(j, py)
        bx_new, by_new = B(j, py), B(j, px)
        adj[ax].remove(bx_old)
        adj[bx_old].remove(ax)
        adj[ay].remove(by_old)
        adj[by_old].remove(ay)
        adj[ax].append(bx_new)
        adj[bx_new].append(ax)
        adj[ay].append(by_new)
        adj[by_new].append(ay)
        p[x], p[y] = py, px

        c2 = _pcost(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            adj[ax].remove(bx_new)
            adj[bx_new].remove(ax)
            adj[ay].remove(by_new)
            adj[by_new].remove(ay)
            adj[ax].append(bx_old)
            adj[bx_old].append(ax)
            adj[ay].append(by_old)
            adj[by_old].append(ay)
            p[x], p[y] = px, py

    if cost != 0:
        return None
    edges = [(v, u) for v in range(k * m) for u in adj[v]]
    return n, edges


# ----------------------------------------------------------------------------
# Secondary family: bi-Cayley voltage lifts over semidirect products, annealed.
# ----------------------------------------------------------------------------

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
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    if cost < _BIG:
        T0 = max(1.0, 0.05 * cost)
    else:
        T0 = 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

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


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 1.0)
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    moore = lib.moore_bound(d, D)

    # Primary: permutation-lift annealing aimed just above a floor near the
    # expected record level, then upward through the candidate orders.
    if D >= 3 and best_n < moore:
        lift_deadline = start + 0.5 * (deadline - start)
        floor_n = max(best_n, int(0.6 * moore))
        cands = _lift_candidates(d, floor_n, moore)
        for n, k, M, m in cands:
            now = time.monotonic()
            if now >= lift_deadline:
                break
            if n <= best_n:
                continue
            slice_end = min(lift_deadline, now + max(2.0, 0.25 * (lift_deadline - now)))
            res = _perm_anneal(d, D, k, m, M, rng, slice_end)
            if res is not None:
                consider(res[0], res[1])

    # Secondary: bi-Cayley voltage lifts over semidirect products for the rest of the budget.
    if D >= 3:
        ks = [1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        iters = 1500 if D >= 5 else 400
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, 3))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
