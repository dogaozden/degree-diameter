import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Core measurement: number of unordered pairs at distance > D (bitset balls).
# ----------------------------------------------------------------------------

def _bad_pairs(n, adj, D):
    """Count unordered vertex pairs not within distance D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# Degree-preserving edge-switch annealing on bipartite graphs.
# Sides: side[v] == 0 is "A", side[v] == 1 is "B". elist holds [a, b] with a in A.
# ----------------------------------------------------------------------------

def _switch(adj, elist, rng):
    """Replace (a,b),(c,e) by (a,e),(c,b). Returns an undo record, or None if illegal."""
    m = len(elist)
    if m < 2:
        return None
    i = rng.randrange(m)
    j = rng.randrange(m)
    if i == j:
        return None
    a, b = elist[i]
    c, e = elist[j]
    if a == c or b == e or e in adj[a] or b in adj[c]:
        return None
    adj[a].discard(b)
    adj[b].discard(a)
    adj[c].discard(e)
    adj[e].discard(c)
    adj[a].add(e)
    adj[e].add(a)
    adj[c].add(b)
    adj[b].add(c)
    elist[i] = [a, e]
    elist[j] = [c, b]
    return (i, j, a, b, c, e)


def _undo(adj, elist, mv):
    i, j, a, b, c, e = mv
    adj[a].discard(e)
    adj[e].discard(a)
    adj[c].discard(b)
    adj[b].discard(c)
    adj[a].add(b)
    adj[b].add(a)
    adj[c].add(e)
    adj[e].add(c)
    elist[i] = [a, b]
    elist[j] = [c, e]


def _anneal(adj, elist, D, rng, deadline, iters):
    """Simulated annealing on edge switches; returns final cost (0 means valid)."""
    n = len(adj)
    cost = _bad_pairs(n, adj, D)
    T0, T1 = 1.0, 0.05
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        mv = _switch(adj, elist, rng)
        if mv is None:
            continue
        c2 = _bad_pairs(n, adj, D)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
            cost = c2
        else:
            _undo(adj, elist, mv)
    return cost


def _insert_pair(adj, side, elist, d, rng):
    """Add one A-vertex and one B-vertex, each of degree d, by splitting d existing edges.

    Every old endpoint keeps its degree. Returns False if no valid choice was found.
    """
    if len(elist) < d:
        return False
    picked = None
    for _ in range(100):
        idx = rng.sample(range(len(elist)), d)
        xs = [elist[i][0] for i in idx]
        ys = [elist[i][1] for i in idx]
        if len(set(xs)) == d and len(set(ys)) == d:
            picked = idx
            break
    if picked is None:
        return False
    drop = set(picked)
    keep = [elist[i] for i in range(len(elist)) if i not in drop]
    n = len(adj)
    a, b = n, n + 1
    adj.append(set())
    adj.append(set())
    side.append(0)
    side.append(1)
    for x, y in zip(xs, ys):
        adj[x].discard(y)
        adj[y].discard(x)
        adj[x].add(b)
        adj[b].add(x)
        adj[y].add(a)
        adj[a].add(y)
        keep.append([x, b])
        keep.append([a, y])
    elist[:] = keep
    return True


def _state(n, edges):
    """Adjacency sets and a 2-colouring of a bipartite graph."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    side = [-1] * n
    for s in range(n):
        if side[s] != -1:
            continue
        side[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if side[v] == -1:
                    side[v] = 1 - side[u]
                    stack.append(v)
    return adj, side


def _saturate(adj, side, d, rng):
    """Add A-B edges between deficient vertices (only shrinks distances)."""
    n = len(adj)
    A = [v for v in range(n) if side[v] == 0 and len(adj[v]) < d]
    B = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]
    rng.shuffle(A)
    rng.shuffle(B)
    for a in A:
        for b in B:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) < d and b not in adj[a]:
                adj[a].add(b)
                adj[b].add(a)


def _elist(adj, side):
    return [[u, v] for u in range(len(adj)) if side[u] == 0 for v in adj[u]]


def _to_edges(adj, side):
    return [(u, v) for u in range(len(adj)) if side[u] == 0 for v in adj[u]]


def _clone(adj, side, elist):
    return [set(s) for s in adj], list(side), [list(e) for e in elist]


def _chain(d, D, rng, deadline, consider, start_pair):
    """Grow a valid graph by pair insertion followed by annealing."""
    n0, e0 = start_pair
    adj, side = _state(n0, e0)
    _saturate(adj, side, d, rng)
    consider(len(adj), _to_edges(adj, side))
    elist = _elist(adj, side)
    fails = 0
    while time.monotonic() < deadline and fails < 8:
        snap = _clone(adj, side, elist)
        if not _insert_pair(adj, side, elist, d, rng):
            break
        cost = _anneal(adj, elist, D, rng, deadline, 2500)
        if cost == 0:
            consider(len(adj), _to_edges(adj, side))
            fails = 0
        else:
            adj, side, elist = snap
            fails += 1


# ----------------------------------------------------------------------------
# Group voltage lifts over Z_m x| Z_k2 (baseline family, annealed).
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


def _lift_anneal(d, D, k, G, mul, rng, deadline, iters):
    """Anneal voltages and layer permutations of a bi-Cayley lift. Returns (n, edges) or None."""
    N = 2 * k * G

    def graph(darts):
        adj = [set() for _ in range(N)]
        for i, j, s in darts:
            for g in range(G):
                a = i * G + g
                b = (k + j) * G + mul(g, s)
                adj[a].add(b)
                adj[b].add(a)
        return adj

    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    adj = graph(darts)
    cost = _bad_pairs(N, adj, D)
    T0, T1 = 1.5, 0.05
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        cand = [row[:] for row in darts]
        if k == 1 or rng.random() < 0.6:
            cand[rng.randrange(len(cand))][2] = rng.randrange(G)
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            cand[ia][1], cand[ib][1] = cand[ib][1], cand[ia][1]
        adj2 = graph(cand)
        c2 = _bad_pairs(N, adj2, D)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
            darts, adj, cost = cand, adj2, c2
    if cost == 0:
        return N, [(a, b) for a in range(k * G) for b in adj[a]]
    return None


def _lift_phase(d, D, best_n, rng, deadline):
    ks = [1, 1, 2, 2, 3, 4]
    found = None
    bn = best_n
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = bn // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, 3))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _lift_anneal(d, D, k, order, mul, rng, deadline, 800)
        if res is not None and res[0] > bn:
            found = res
            bn = res[0]
    return found


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best = [n0, e0]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    try:
        # Fast path: projective plane meets the Moore bound when d-1 is a prime power.
        if D == 3 and lib.is_prime_power(d - 1):
            n, e = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n, e, d, D):
                return n, e

        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])

        # Baseline: voltage-lift search for D >= 4, a short slice of the budget.
        if D >= 4:
            res = _lift_phase(d, D, best[0], rng, start + 0.3 * time_limit)
            if res is not None:
                consider(res[0], res[1])

        # Main phase: grow the best graph by pair insertion and edge-switch annealing.
        if D >= 3:
            _chain(d, D, rng, start + 0.88 * time_limit, consider,
                   (best[0], best[1]))
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = [n0, e0]
    return best[0], best[1]
