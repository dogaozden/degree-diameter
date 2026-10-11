import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs.
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


# ----------------------------------------------------------------------------
# New construction: bi-Cayley (group-lift) graphs.
#
# Pick a finite group G of order M and a connection set S of d elements.
# Vertices A_x and B_y (x, y in G); edges A_x -- B_{x*s} for s in S.
# This is a d-regular bipartite graph on 2M vertices, and G acts transitively
# on each side by left multiplication. So the diameter is at most D iff the
# D-ball around A_e covers all vertices and the D-ball around B_e covers all
# vertices. Search for S by hill climbing over several groups per order M.
# ----------------------------------------------------------------------------

_SLICE = 0.8  # seconds per (order, group) attempt


def _group_specs(M, rng, limit=3):
    """Cyclic group plus up to limit-1 random nonabelian semidirect products Z_a x| Z_k of order M."""
    sd = []
    for k in range(2, M):
        if M % k:
            continue
        a = M // k
        if a < 3:
            continue
        for r in range(2, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a:
                sd.append((a, k, r))
    rng.shuffle(sd)
    return [None] + sd[:limit - 1]


def _group_tables(M, spec):
    """Multiplication table T[x][y] = x*y and inverse list I for the group of order M."""
    if spec is None:
        _, mul, inv = lib.cyclic_group(M)
    else:
        _, mul, inv = lib.semidirect_group(*spec)
    T = [[mul(x, y) for y in range(M)] for x in range(M)]
    I = [inv(x) for x in range(M)]
    return T, I


def _bicayley_adj(T, I, M, S):
    """Adjacency lists of the bi-Cayley graph: A_x = x, B_y = M + y."""
    Sinv = [I[s] for s in S]
    adj = [[M + row[s] for s in S] for row in T]
    adj += [[row[t] for t in Sinv] for row in T]
    return adj


def _reach_count(adj, src, D):
    """Number of vertices within distance D of src."""
    seen = {src}
    frontier = [src]
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if v not in seen:
                    seen.add(v)
                    nxt.append(v)
        if not nxt:
            break
        frontier = nxt
    return len(seen)


def _score(T, I, M, S, D):
    """Number of vertices not covered from A_e plus from B_e (0 means diameter <= D)."""
    adj = _bicayley_adj(T, I, M, S)
    n2 = 2 * M
    return (n2 - _reach_count(adj, 0, D)) + (n2 - _reach_count(adj, M, D))


def _search_group(M, spec, d, D, deadline, rng):
    """Hill climb over d-subsets of G; return (S, T) with score 0, or None."""
    T, I = _group_tables(M, spec)
    S = rng.sample(range(M), d)
    cur = _score(T, I, M, S, D)
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        g = rng.randrange(M)
        if g in S:
            continue
        S2 = list(S)
        S2[i] = g
        sc = _score(T, I, M, S2, D)
        if sc <= cur or rng.random() < 0.01:
            S, cur = S2, sc
    if cur == 0:
        return S, T
    return None


def _bicayley_search(d, D, deadline, rng, m_start):
    """Scan group orders M upward from m_start; return the largest valid (n, edges) found."""
    best = None
    M = max(m_start, d + 1)
    fails = 0
    while time.monotonic() < deadline and fails < 3:
        ok = None
        for spec in _group_specs(M, rng):
            now = time.monotonic()
            if now >= deadline:
                break
            end = min(deadline, now + _SLICE)
            res = _search_group(M, spec, d, D, end, rng)
            if res is None:
                continue
            S, T = res
            edges = [(x, M + T[x][s]) for x in range(M) for s in S]
            if lib.is_valid(2 * M, edges, d, D):
                ok = (2 * M, edges)
                break
        if ok is None:
            fails += 1
        else:
            fails = 0
            if best is None or ok[0] > best[0]:
                best = ok
        M += 1
    return best


# ----------------------------------------------------------------------------
# Graph utilities.
# ----------------------------------------------------------------------------

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


def _balls_radius(n, adj, r):
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


# ----------------------------------------------------------------------------
# Twin blow-up with spare-capacity packing (used on the GQ base for D = 4).
# ----------------------------------------------------------------------------

def _pack(R, cap, n, rng, deadline, iters):
    """Choose candidates so that each resource u is used by at most cap[u] chosen candidates."""
    k = len(R)
    if k == 0:
        return []
    users = [[] for _ in range(n)]
    for i, r in enumerate(R):
        for u in r:
            users[u].append(i)
    load = [0] * n
    inS = [False] * k
    S = set()

    def add(i):
        inS[i] = True
        S.add(i)
        for u in R[i]:
            load[u] += 1

    def remove(i):
        inS[i] = False
        S.discard(i)
        for u in R[i]:
            load[u] -= 1

    order = list(range(k))
    rng.shuffle(order)
    for i in order:
        if all(load[u] < cap[u] for u in R[i]):
            add(i)
    best = list(S)

    for _ in range(iters):
        if time.monotonic() > deadline:
            break
        i = rng.randrange(k)
        if inS[i]:
            continue
        removed = []
        for u in R[i]:
            while load[u] >= cap[u]:
                j = rng.choice([x for x in users[u] if inS[x]])
                remove(j)
                removed.append(j)
        add(i)
        delta = 1 - len(removed)
        if delta < 0 and rng.random() >= 0.03:
            remove(i)
            for j in removed:
                add(j)
        if len(S) > len(best):
            best = list(S)
    return best


def _twin_pass(n, edges, d, side, rng, deadline, iters):
    """Twin as many vertices of one side as the spare degree of the other side allows."""
    adj = _adjacency(n, edges)
    color = _bipartition(n, adj)
    deg = [len(a) for a in adj]
    capv = [d - deg[u] for u in range(n)]
    cands = [v for v in range(n)
             if color[v] == side and adj[v] and all(capv[u] >= 1 for u in adj[v])]
    if not cands:
        return n, edges
    R = [adj[v] for v in cands]
    chosen = _pack(R, capv, n, rng, deadline, iters)
    if not chosen:
        return n, edges
    new_edges = list(edges)
    nn = n
    for i in chosen:
        v = cands[i]
        for u in adj[v]:
            new_edges.append((u, nn))
        nn += 1
    return nn, new_edges


# ----------------------------------------------------------------------------
# Cover-based vertex extension (diameter-preserving growth).
# ----------------------------------------------------------------------------

def _greedy_cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng, always_random=False):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(40):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng,
                                       always_random or attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Add random edges between non-adjacent opposite-side vertices with spare degree."""
    edges = list(edges)
    adj = _adjacency(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _expand(n, edges, d, D, deadline, rng, rounds=6):
    """Alternate twin packing on both sides with cover growth, while the graph keeps growing."""
    cur_n, cur_e = n, list(edges)
    for _ in range(rounds):
        if time.monotonic() >= deadline:
            break
        n0 = cur_n
        for side in (0, 1):
            iters = rng.choice([3000, 10000, 30000])
            cur_n, cur_e = _twin_pass(cur_n, cur_e, d, side, rng, deadline, iters)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == n0:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best
    if d == 2:
        consider(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])
        return best

    # Already at the Moore bound: nothing to gain.
    if best[0] >= lib.moore_bound(d, D):
        return best

    # Calibration / D = 3 bases: projective-plane incidence graphs.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        if best[0] >= lib.moore_bound(d, D):
            return best

    # New construction: bi-Cayley graphs over groups of order M, searched upward from M0.
    bc_deadline = start + 0.45 * T
    m_start = max(d + 1, lib.moore_bound(d, D) // 4)
    try:
        bc = _bicayley_search(d, D, bc_deadline, rng, m_start)
    except Exception:
        bc = None
    if bc is not None:
        consider(bc[0], bc[1])
        try:
            gn, ge = _grow(bc[0], bc[1], d, D, start + 0.55 * T, rng)
            consider(gn, ge)
        except Exception:
            pass

    # Previous construction (kept as a second route): GQ W(q) base plus expansion, for D = 4.
    if D == 4:
        gq_deadline = start + 0.75 * T
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            if time.monotonic() >= gq_deadline:
                break
            try:
                base = _gq_w(q)
                consider(base[0], base[1])
                n2, e2 = _expand(base[0], base[1], d, D, gq_deadline, rng)
                consider(n2, e2)
            except Exception:
                pass

    # Final growth pass on the best graph.
    try:
        gn, ge = _grow(best[0], best[1], d, D, start + 0.85 * T, rng)
        consider(gn, ge)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
