import itertools
import math
import random
import time

import lib


# ============================================================================
# Bi-Cayley engine (main search).
# Vertices a_x (x in G) and b_y (y in G); a_x ~ b_{x*s} for s in S, |S| = d.
# Left multiplication by G is an automorphism, so only the two representatives
# a_e and b_e need BFS. Simulated annealing on S minimises the number of
# (representative, vertex) pairs at distance > D. Every candidate is re-checked
# with lib.is_valid before it is accepted.
# ============================================================================

def _bc_group(G, rng):
    """Random semidirect product Z_m x| Z_k of order G, as (order, mul, inv), or None."""
    opts = []
    for k in range(1, 13):
        if G % k:
            continue
        m = G // k
        if k == 1:
            opts.append((m, 1, 1))
            continue
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    if not opts:
        return None
    m, k, r = rng.choice(opts)
    return lib.semidirect_group(m, k, r)


def _bc_count(Gs, S, invS, Mt, D, src):
    """Number of vertices within distance D of src in the bi-Cayley graph."""
    seen = bytearray(2 * Gs)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < Gs:
                row = Mt[u]
                for s in S:
                    v = Gs + row[s]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                row = Mt[u - Gs]
                for t in invS:
                    v = row[t]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        if not nxt:
            break
        cnt += len(nxt)
        frontier = nxt
    return cnt


def _bc_cost(Gs, S, D, Mt, invt):
    """Pairs (representative, vertex) at distance > D. Zero means valid."""
    invS = [invt[s] for s in S]
    a = _bc_count(Gs, S, invS, Mt, D, 0)
    b = _bc_count(Gs, S, invS, Mt, D, Gs)
    return 4 * Gs - a - b


def _bc_anneal(Gs, d, D, Mt, invt, rng, deadline):
    """Anneal a d-element connection set; return it when cost is zero, else None."""
    S = rng.sample(range(Gs), d)
    cur = _bc_cost(Gs, S, D, Mt, invt)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        temp = 1.0 * (0.02 ** ((now - t0) / span)) + 1e-3
        i = rng.randrange(d)
        g = rng.randrange(Gs)
        if g in S:
            continue
        old = S[i]
        S[i] = g
        c = _bc_cost(Gs, S, D, Mt, invt)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            S[i] = old
    return list(S) if cur == 0 else None


def _bc_search(d, D, rng, floor_n, deadline):
    """Search bi-Cayley graphs of order 2G above the current floor; return best valid or None."""
    best = None
    floor = floor_n
    hi_cap = lib._moore_bound(d, D) // 2
    while time.monotonic() < deadline:
        lo = max(floor // 2 + 1, d)
        hi = min(hi_cap, lo + 25)
        if hi < lo:
            break
        G = rng.randint(lo, hi)
        grp = _bc_group(G, rng)
        if grp is None:
            continue
        Gs, mul, inv = grp
        Mt = [[mul(x, y) for y in range(Gs)] for x in range(Gs)]
        invt = [inv(x) for x in range(Gs)]
        slice_end = min(deadline, time.monotonic() + 3.0)
        S = _bc_anneal(Gs, d, D, Mt, invt, rng, slice_end)
        if S is not None:
            E = [(x, Gs + Mt[x][s]) for x in range(Gs) for s in S]
            n = 2 * Gs
            if n > floor and lib.is_valid(n, E, d, D):
                best = (n, E)
                floor = n
    return best


# ============================================================================
# Safe bases and augmentation.
# ============================================================================

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


def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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


def _max_b_matching(n, edges, d, color, rng):
    """Maximum set of new cross edges respecting degree <= d (augmenting paths)."""
    deg = [0] * n
    existing = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        existing.add((min(u, v), max(u, v)))
    spare = [d - deg[v] for v in range(n)]
    L = [v for v in range(n) if color[v] == 0 and spare[v] > 0]
    R = [v for v in range(n) if color[v] == 1 and spare[v] > 0]
    rng.shuffle(L)
    rng.shuffle(R)
    mL = {a: set() for a in L}
    mR = {b: set() for b in R}

    while True:
        parent_left = {}
        parent_right = {}
        queue = []
        for a in L:
            if spare[a] - len(mL[a]) > 0:
                parent_left[a] = None
                queue.append(a)
        found = None
        qi = 0
        while qi < len(queue) and found is None:
            a = queue[qi]
            qi += 1
            for b in R:
                if b in parent_right or b in mL[a]:
                    continue
                if (min(a, b), max(a, b)) in existing:
                    continue
                parent_right[b] = a
                if spare[b] - len(mR[b]) > 0:
                    found = b
                    break
                for a2 in mR[b]:
                    if a2 not in parent_left:
                        parent_left[a2] = b
                        queue.append(a2)
        if found is None:
            break
        b = found
        while True:
            a = parent_right[b]
            mL[a].add(b)
            mR[b].add(a)
            pb = parent_left[a]
            if pb is None:
                break
            mL[a].discard(pb)
            mR[pb].discard(a)
            b = pb
    return [(a, b) for a in L for b in mL[a]]


def _saturate_edges(n, edges, d, rng):
    """Add new cross edges with spare degree; never increases distances."""
    edges = list(edges)
    adj = _adjacency(n, edges)
    color = _bipartition(n, adj)
    return edges + _max_b_matching(n, edges, d, color, rng)


# ============================================================================
# Driver.
# ============================================================================

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = time_limit
    deadline = start + 0.80 * T
    rng = random.Random(seed * 1000003 + d * 101 + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if best[0] >= lib._moore_bound(d, D):
        return best

    # Algebraic base graphs, augmented by degree-respecting cross edges.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            consider(pg[0], _saturate_edges(pg[0], pg[1], d, rng))
    elif D >= 4:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:1]
        for q in qs:
            bn, be = _gq_w(q)
            consider(bn, be)
            consider(bn, _saturate_edges(bn, be, d, rng))

    # Main engine: bi-Cayley annealing, which aims above the current best.
    res = _bc_search(d, D, rng, best[0], start + 0.85 * T)
    if res is not None:
        consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
