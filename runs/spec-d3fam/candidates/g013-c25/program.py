import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _araujo(d):
    """Araujo-Pardo & Lopez record graph (degree q+2) when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, AssertionError):
        return None


def _pg_regular(d):
    """Incidence graph of PG(2, d-1) when d-1 is a prime power: d-regular, diameter 3."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q); (q+1)-regular, diameter 4."""
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


def _gq_regular(d):
    """W(q) when d-1 = q is a small prime power (degree q+1 = d)."""
    q = d - 1
    if 2 <= q <= 9 and lib.is_prime_power(q):
        return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW: regular pair-insertion with diameter-checked acceptance.
#
# For a d-regular bipartite graph, pick d vertices T on one side, and for each
# t in T delete one edge (t, y_t) with all y_t distinct. Add a new vertex w of
# the same side as the y's, joined to T, and a new vertex u on the other side,
# joined to all y_t. Every old vertex keeps degree d, so the graph stays
# d-regular and bipartite with 2 more vertices. Accept only if the diameter
# is still <= D (checked with bitmask balls).
# ----------------------------------------------------------------------------

def _bip_sets(n, adj):
    """Two-colouring of a bipartite graph given by adjacency sets."""
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


def _diam_ok(n, adj, D):
    """True iff every pair of vertices is within distance D."""
    full = (1 << n) - 1
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return all(r == full for r in reach)


def _insert_pairs(n, edges, d, D, deadline, rng, max_fail=4000):
    """Grow a d-regular bipartite graph by two vertices at a time, keeping diameter <= D."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    if any(len(a) != d for a in adj):
        return n, list(edges)
    color = _bip_sets(n, adj)
    fails = 0
    while fails < max_fail and time.monotonic() < deadline:
        c = rng.randrange(2)
        side = [v for v in range(n) if color[v] == 1 - c]
        if len(side) < d:
            break
        T = rng.sample(side, d)
        used = set()
        pairs = []
        ok = True
        for t in T:
            cand = [y for y in adj[t] if y not in used]
            if not cand:
                ok = False
                break
            y = rng.choice(cand)
            used.add(y)
            pairs.append((t, y))
        if not ok:
            fails += 1
            continue

        w, u = n, n + 1
        for t, y in pairs:
            adj[t].discard(y)
            adj[y].discard(t)
        adj.append(set())
        adj.append(set())
        for t, _ in pairs:
            adj[w].add(t)
            adj[t].add(w)
        for _, y in pairs:
            adj[u].add(y)
            adj[y].add(u)

        if _diam_ok(n + 2, adj, D):
            n += 2
            color.append(c)
            color.append(1 - c)
            fails = 0
        else:
            for t, _ in pairs:
                adj[t].discard(w)
            for _, y in pairs:
                adj[y].discard(u)
            adj.pop()
            adj.pop()
            for t, y in pairs:
                adj[t].add(y)
                adj[y].add(t)
            fails += 1

    out = [(a, b) for a in range(n) for b in adj[a] if a < b]
    return n, out


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products, annealed (fallback family).
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
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
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

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Regular bases whose spare structure admits pair insertion.
    bases = []
    if D >= 3:
        rec = _araujo(d)
        if rec is not None:
            bases.append(rec)
        pg = _pg_regular(d)
        if pg is not None:
            bases.append(pg)
    if D >= 4:
        gq = _gq_regular(d)
        if gq is not None:
            bases.append(gq)

    for b_n, b_e in bases:
        consider(b_n, b_e)

    # Pair-insertion growth: each base gets an equal share of the remaining time.
    for idx, (b_n, b_e) in enumerate(bases):
        now = time.monotonic()
        share = max(0.0, deadline - now) / (len(bases) - idx)
        n2, e2 = _insert_pairs(b_n, b_e, d, D, now + share,
                               random.Random(seed * 104729 + idx))
        consider(n2, e2)

    # Fallback search for cases with no regular base: annealed group voltage lifts.
    if not bases:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
