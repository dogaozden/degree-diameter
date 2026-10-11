import itertools
import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Basic graph utilities.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Two-colouring of adjacency (list of sets/lists); None if not bipartite."""
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
                elif color[v] == color[u]:
                    return None
    return color


def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable counts)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# Structured bases: projective plane (D = 3) and generalized quadrangle W(q) (D = 4).
# ----------------------------------------------------------------------------

def _largest_pp_at_most(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _gq_w(q):
    """Incidence graph of points and lines of W(q); diameter 4."""
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
# Bi-Cayley voltage lifts over Z_m x| Z_k (annealed). Used to find a strong
# starting graph for the unstructured stage.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
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


def _lift_cost(k, G, D, darts, perms):
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


def _lift_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)

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
            c2 = _lift_cost(k, G, D, darts, perms)
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
            c2 = _lift_cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _lift_edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Unstructured stage: grow by two vertices, repair with degree-preserving swaps.
#
# State: a bipartite graph with max degree d, stored as an edge list E of pairs
# (a, b) with color[a] = 0 and color[b] = 1. A swap replaces (a,b),(c,d) by
# (a,d),(c,b), which keeps every degree. Cost = pairs at distance > D.
# Growth removes one edge (x,y) and adds new vertices v (side 0) and u (side 1)
# with edges (v,y), (x,u), (v,u); this keeps all old degrees and sets v,u to 2.
# Remaining spare degree is filled greedily by adding edges (never hurts).
# ----------------------------------------------------------------------------

def _grow_search(n0, edges0, d, D, deadline, rng, report):
    n = n0
    adj = [set() for _ in range(n)]
    for u, v in edges0:
        adj[u].add(v)
        adj[v].add(u)
    color = _bipartition(n, adj)
    if color is None:
        return
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges0]
    if len(E) < 2:
        return
    S = set(E)

    def fill():
        A = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
        B = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
        pairs = [(a, b) for a in A for b in B if b not in adj[a]]
        rng.shuffle(pairs)
        for a, b in pairs:
            if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
                adj[a].add(b)
                adj[b].add(a)
                E.append((a, b))
                S.add((a, b))

    def grow():
        nonlocal n
        i = rng.randrange(len(E))
        x, y = E[i]
        v, u = n, n + 1
        n += 2
        adj.append(set())
        adj.append(set())
        color.append(0)
        color.append(1)
        adj[x].discard(y)
        adj[y].discard(x)
        S.discard((x, y))
        E[i] = (v, y)
        S.add((v, y))
        adj[v].add(y)
        adj[y].add(v)
        for a, b in ((x, u), (v, u)):
            E.append((a, b))
            S.add((a, b))
            adj[a].add(b)
            adj[b].add(a)
        fill()

    cost = _bad_pairs(n, adj, D)
    step = 0
    L = 3000
    while time.monotonic() < deadline:
        if cost == 0:
            report(n, list(E))
            grow()
            cost = _bad_pairs(n, adj, D)
            step = 0
            continue

        step = (step + 1) % L
        T = 1.5 * (0.15 ** (step / L))
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a, b = E[i]
        c, dd = E[j]
        if a == c or b == dd:
            continue
        na, nc = (a, dd), (c, b)
        if na in S or nc in S:
            continue

        # Apply swap.
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(dd); adj[dd].discard(c)
        adj[a].add(dd); adj[dd].add(a)
        adj[c].add(b); adj[b].add(c)
        S.discard((a, b)); S.discard((c, dd))
        S.add(na); S.add(nc)
        E[i] = na
        E[j] = nc

        c2 = _bad_pairs(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            # Revert swap.
            adj[a].discard(dd); adj[dd].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(dd); adj[dd].add(c)
            S.discard(na); S.discard(nc)
            S.add((a, b)); S.add((c, dd))
            E[i] = (a, b)
            E[j] = (c, dd)


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Structured starts.
    if D == 3:
        q = _largest_pp_at_most(d - 1)
        if q is not None:
            consider(*lib.projective_plane_incidence(q))
            if q == d - 1:
                # Moore-optimal for D = 3: nothing larger exists.
                return best
    if D == 4:
        q = _largest_pp_at_most(min(d - 1, 9))
        if q is not None:
            consider(*_gq_w(q))

    # Stage A: lift search for a strong starting graph.
    deadline_a = start + 0.35 * time_limit
    deadline_b = start + 0.85 * time_limit
    if D >= 5:
        ks = [1, 1, 2, 2, 3, 4]
        anneal_iters = 1500
    else:
        ks = [1, 1, 2, 3]
        anneal_iters = 400
    while time.monotonic() < deadline_a:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        if D >= 5:
            G = max(2, base + 1 + rng.randrange(0, 3))
        else:
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal_lift(d, D, k, order, mul, rng, deadline_a, iters=anneal_iters)
        if res is not None:
            consider(res[0], res[1])

    # Stage B: unstructured growth from the best graph found so far.
    if time.monotonic() < deadline_b:
        _grow_search(best[0], best[1], d, D, deadline_b, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
