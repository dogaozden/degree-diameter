import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _largest_pp(x, cap):
    """Largest prime power q with 2 <= q <= min(x, cap), or None."""
    for q in range(min(x, cap), 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4.
    Points are 0..P-1 (colour 0), lines are P..2P-1 (colour 1)."""
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
# Helpers on mutable adjacency sets.
# ----------------------------------------------------------------------------

def _to_edges(adj, color):
    return [(a, b) for a in range(len(adj)) if color[a] == 0 for b in adj[a]]


def _bad(n, adj, D):
    """Number of unordered pairs at distance > D (bitmask balls)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _add_matching(n, P, adj, d, rng):
    """Use spare degree: join deficient points to deficient non-incident lines."""
    fp = [p for p in range(P) if len(adj[p]) < d]
    fl = [L for L in range(P, n) if len(adj[L]) < d]
    rng.shuffle(fl)
    for p in fp:
        for L in fl:
            if len(adj[p]) >= d:
                break
            if len(adj[L]) < d and L not in adj[p]:
                adj[p].add(L)
                adj[L].add(p)


# ----------------------------------------------------------------------------
# New idea: insert one vertex, then repair by degree-preserving edge-swap
# annealing (plus edges between deficient opposite vertices, which never hurt).
# ----------------------------------------------------------------------------

def _try_insert(adj, color, d, D, deadline, rng, iters):
    """Mutates adj/color by appending one vertex. Returns True iff the result has diameter <= D."""
    v = len(adj)
    c = rng.randrange(2)
    adj.append(set())
    color.append(c)
    opp = [u for u in range(v) if color[u] != c]
    rng.shuffle(opp)
    opp.sort(key=lambda u: len(adj[u]) >= d)  # spare-degree vertices first
    for u in opp[:d]:
        if len(adj[u]) >= d:
            x = rng.choice(sorted(adj[u]))  # free one slot, keeps bipartiteness
            adj[u].discard(x)
            adj[x].discard(u)
        adj[u].add(v)
        adj[v].add(u)

    N = len(adj)
    E = _to_edges(adj, color)
    cost = _bad(N, adj, D)
    it = 0
    while cost > 0 and it < iters and time.monotonic() < deadline:
        it += 1
        T = 0.5 * (0.05 ** (it / iters))
        if rng.random() < 0.3:
            A = [a for a in range(N) if color[a] == 0 and len(adj[a]) < d]
            B = [b for b in range(N) if color[b] == 1 and len(adj[b]) < d]
            if not A or not B:
                continue
            a = rng.choice(A)
            b = rng.choice(B)
            if b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            E.append((a, b))
            cost = _bad(N, adj, D)  # adding edges never increases cost
            continue
        if len(E) < 2:
            break
        i, j = rng.sample(range(len(E)), 2)
        a, b = E[i]
        x, y = E[j]
        if a == x or b == y or y in adj[a] or b in adj[x]:
            continue
        adj[a].discard(b); adj[b].discard(a)
        adj[x].discard(y); adj[y].discard(x)
        adj[a].add(y); adj[y].add(a)
        adj[x].add(b); adj[b].add(x)
        new = _bad(N, adj, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
            E[i] = (a, y)
            E[j] = (x, b)
        else:
            adj[a].discard(y); adj[y].discard(a)
            adj[x].discard(b); adj[b].discard(x)
            adj[a].add(b); adj[b].add(a)
            adj[x].add(y); adj[y].add(x)
    return cost == 0


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    best = fallback
    if D not in (3, 4):
        return best

    q = _largest_pp(d - 1, 23 if D == 3 else 9)
    if q is None:
        return best
    if D == 3:
        n, edges = lib.projective_plane_incidence(q)
    else:
        n, edges = _gq_w(q)
    if not lib.is_valid(n, edges, d, D):
        return best
    best = (n, edges)

    P = n // 2
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = [0] * P + [1] * P
    _add_matching(n, P, adj, d, rng)
    E0 = _to_edges(adj, color)
    if len(E0) > len(best[1]) and lib.is_valid(n, E0, d, D):
        best = (n, E0)

    # Insert-and-repair loop on the current graph.
    while time.monotonic() < deadline:
        snap = [set(s) for s in adj]
        csnap = color[:]
        ok = _try_insert(adj, color, d, D, deadline, rng, 600)
        if ok:
            N = len(adj)
            E = _to_edges(adj, color)
            if N > best[0] and lib.is_valid(N, E, d, D):
                best = (N, E)
                continue
        adj = snap
        color = csnap

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
