"""Bipartite (d, D) graph builder.

Pipeline:
  1. Baselines: K_{d,d}, projective-plane incidence, Araujo-Pardo-Lopez graph.
  2. Bi-Cayley voltage lifts over Z_m x| Z_k (k in {1, 2}), annealed on a
     cheap BFS-from-block-representatives cost.
  3. NEW: regular-bipartite augmentation by edge splicing plus swap annealing.
     Take a d-regular bipartite graph G. Pick d edges x_t y_t with distinct
     x's and distinct y's, delete them, add a new A-vertex a adjacent to all
     y_t and a new B-vertex b adjacent to all x_t. Every degree stays d and
     the graph stays bipartite, so it grows by 2 vertices. Then anneal with
     degree-preserving double-edge swaps (x1,y1),(x2,y2) -> (x1,y2),(x2,y1)
     to drive the number of pairs at distance > D to zero. Each success is
     checked and becomes the new base for further insertions.
"""
import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Baselines
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Projective-plane incidence graph for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2, q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Generic graph helpers (adjacency given as lists or sets)
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


def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
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


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (0 means diameter <= D)."""
    ball = _balls(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over Z_m x| Z_k2
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
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


def _lift_cost(k, G, D, darts, perms):
    """Pairs (block representative, vertex) not reached within D. Zero iff the lift has diameter <= D.

    The lift is invariant under left translation within each block, so one
    representative per block suffices.
    """
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba, bb = i * G, (k + j) * G
        for g in range(G):
            a, b = ba + g, bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
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


def _lift_anneal(d, D, k, G, mul, rng, deadline, iters):
    """Anneal voltages of a random d-regular bi-Cayley lift. Returns (darts, perms, cost)."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        idx = rng.randrange(len(darts))
        new = rng.randrange(G)
        old = darts[idx][2]
        if new == old:
            continue
        oldp = perms[idx]
        darts[idx][2] = new
        perms[idx] = [mul(g, new) for g in range(G)]
        c2 = _lift_cost(k, G, D, darts, perms)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            darts[idx][2] = old
            perms[idx] = oldp
    return darts, perms, cost


# ----------------------------------------------------------------------------
# NEW: regular-bipartite augmentation by edge splicing + swap annealing
# ----------------------------------------------------------------------------

def _replace(adj, elist, i, new):
    """Replace the edge stored at elist[i] by `new` (both given as (A-side, B-side))."""
    x, y = elist[i]
    adj[x].discard(y)
    adj[y].discard(x)
    x, y = new
    adj[x].add(y)
    adj[y].add(x)
    elist[i] = new


def _insert_pair(n, adj, elist, d, rng):
    """Add a new A-vertex a = n and B-vertex b = n + 1 by splicing d disjoint edges.

    Each chosen edge (x, y) becomes (x, b) and (a, y); x and y keep their degree,
    a and b get degree d. Returns False if d disjoint edges cannot be found.
    """
    idxs = list(range(len(elist)))
    rng.shuffle(idxs)
    xs, ys, chosen = set(), set(), []
    for idx in idxs:
        x, y = elist[idx]
        if x in xs or y in ys:
            continue
        xs.add(x)
        ys.add(y)
        chosen.append(idx)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return False
    a, b = n, n + 1
    adj.append(set())
    adj.append(set())
    for idx in chosen:
        x, y = elist[idx]
        adj[x].discard(y)
        adj[y].discard(x)
        adj[x].add(b)
        adj[b].add(x)
        adj[a].add(y)
        adj[y].add(a)
        elist[idx] = (x, b)
        elist.append((a, y))
    return True


def _anneal_bad(n, adj, elist, D, rng, deadline):
    """Degree-preserving double-edge swaps minimizing bad pairs. True iff diameter <= D reached."""
    cur = _bad(n, adj, D)
    T = 0.6
    while cur > 0:
        if time.monotonic() > deadline:
            return False
        m = len(elist)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        x1, y1 = elist[i]
        x2, y2 = elist[j]
        if x1 == x2 or y1 == y2 or y2 in adj[x1] or y1 in adj[x2]:
            continue
        old1, old2 = (x1, y1), (x2, y2)
        _replace(adj, elist, i, (x1, y2))
        _replace(adj, elist, j, (x2, y1))
        c2 = _bad(n, adj, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
        else:
            _replace(adj, elist, j, old2)
            _replace(adj, elist, i, old1)
        T = max(0.15, T * 0.9995)
    return True


# ----------------------------------------------------------------------------
# Main entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.8 * time_limit
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    base = lib.haar_graph(d, range(d))
    best_n, best_e = base[0], list(base[1])
    ub = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if best_n >= ub or D < 3:
        return best_n, best_e

    pg = _pg_base(d)
    if pg is not None:
        consider(pg[0], pg[1])
    ar = _araujo(d)
    if ar is not None:
        consider(ar[0], ar[1])
    if best_n >= ub:
        return best_n, best_e

    # Phase 1: voltage-lift search for a large base graph.
    lift_deadline = start + 0.3 * total
    ks = [1, 1, 2]
    while time.monotonic() < lift_deadline and best_n < ub:
        k = rng.choice(ks)
        b0 = best_n // (2 * k)
        lo = max(2, b0 + 1)
        hi = lo + max(3, lo // 6)
        G = rng.randint(lo, hi)
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        darts, perms, c = _lift_anneal(d, D, k, order, mul, rng, lift_deadline, 1200)
        if c == 0:
            n, e = _lift_edges(k, order, darts, perms)
            consider(n, e)

    # Phase 2: grow the best base by edge-splice insertion plus swap annealing.
    if best_n < ub and time.monotonic() < deadline:
        adj = [set() for _ in range(best_n)]
        for u, v in best_e:
            adj[u].add(v)
            adj[v].add(u)
        color = _bipartition(best_n, adj)
        elist = [(u, v) if color[u] == 0 else (v, u) for u, v in best_e]
        sn, sadj, sel = best_n, adj, elist
        att_len = max(0.5, 0.08 * time_limit)
        while time.monotonic() < deadline and sn < ub:
            cn = sn
            cadj = [set(s) for s in sadj]
            cel = list(sel)
            if not _insert_pair(cn, cadj, cel, d, rng):
                break
            cn += 2
            att_deadline = min(deadline, time.monotonic() + att_len)
            if _anneal_bad(cn, cadj, cel, D, rng, att_deadline):
                sn, sadj, sel = cn, cadj, cel
                consider(sn, [(x, y) for x, y in sel])

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = base[0], list(base[1])
    return best_n, best_e
