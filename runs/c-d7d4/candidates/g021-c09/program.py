import itertools
import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers.
# ----------------------------------------------------------------------------

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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


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


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods cover deficient vertices."""
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
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
    """Join deficient opposite-side vertices. Only shortens distances, keeps bipartiteness."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
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


# ----------------------------------------------------------------------------
# Bold new construction: Haar graphs of finite groups, found by annealing.
#
# Take a group G of order M and a connection set S of d distinct elements.
# The bipartite graph with parts {a_x} and {b_y}, joining a_x to b_{xs} for
# s in S, is d-regular on 2M vertices, and left multiplication by g is an
# automorphism that is transitive on each part. So the diameter is at most D
# exactly when the ball of radius D around a_e covers all 2M vertices and the
# ball around b_e does too. That is only two BFS runs per evaluation, so the
# search over S is cheap. Non-abelian groups (semidirect products) avoid the
# commutativity that caps abelian Haar graphs. Annealing over S for a target
# order M, and raising M after each success, searches for orders above the
# current best.
# ----------------------------------------------------------------------------

def _group_descs(M, rng, cap):
    """Descriptors of groups of order M: cyclic, and Z_m x|_r Z_k with m*k = M."""
    out = [("c", M)]
    for k in range(2, M + 1):
        if M % k:
            continue
        m = M // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append(("s", m, k, r))
    rng.shuffle(out)
    return out[:cap]


def _group_tables(desc):
    """Return (order, multiplication table T, inverse list)."""
    if desc[0] == "c":
        order, mul, inv = lib.cyclic_group(desc[1])
    else:
        order, mul, inv = lib.semidirect_group(desc[1], desc[2], desc[3])
    M = order
    T = [[mul(x, s) for s in range(M)] for x in range(M)]
    invs = [inv(s) for s in range(M)]
    return M, T, invs


def _ball_count(src, M, T, S, Sinv, D):
    """Number of vertices within distance D of src in the Haar graph (a_x = x, b_y = M + y)."""
    seen = bytearray(2 * M)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for v in frontier:
            if v < M:
                row = T[v]
                for s in S:
                    w = M + row[s]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            else:
                row = T[v - M]
                for si in Sinv:
                    w = row[si]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
        cnt += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return cnt


def _haar_cost(M, T, S, Sinv, D):
    """Zero iff the Haar graph has diameter <= D (two BFS runs suffice by transitivity)."""
    return (2 * M - _ball_count(0, M, T, S, Sinv, D)) + \
           (2 * M - _ball_count(M, M, T, S, Sinv, D))


def _sa_group(M, T, inv, d, D, rng, iters, deadline):
    """Anneal a connection set S of size d; return it on success, else None."""
    S = rng.sample(range(M), d)
    Sinv = [inv[s] for s in S]
    cur = _haar_cost(M, T, S, Sinv, D)
    for it in range(iters):
        if cur == 0:
            return list(S)
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = 1.5 * (1 - it / iters) + 0.05
        i = rng.randrange(d)
        new = rng.randrange(M)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        Sinv_new = [inv[s] for s in S]
        c = _haar_cost(M, T, S, Sinv_new, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
            Sinv = Sinv_new
        else:
            S[i] = old
    return list(S) if cur == 0 else None


def _group_search(d, D, lo, hi, deadline, rng, consider):
    """For increasing orders M in [lo, hi], search groups and sets S for a valid Haar graph."""
    target = lo
    while time.monotonic() < deadline and target <= hi:
        found = False
        for desc in _group_descs(target, rng, 4):
            if time.monotonic() >= deadline:
                break
            M, T, invs = _group_tables(desc)
            S = _sa_group(M, T, invs, d, D, rng, 800, deadline)
            if S is not None:
                edges = [(x, M + T[x][s]) for x in range(M) for s in S]
                consider(2 * M, edges)
                found = True
                break
        if found:
            target += 1


# ----------------------------------------------------------------------------
# Large-neighbourhood search (kill, repair, regrow), from the best valid graph.
# ----------------------------------------------------------------------------

def _cost(adj, D):
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _fill(adj, color, d, rng):
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(adj, color, d, D, rng, iters, deadline):
    """Degree-preserving bipartite switches minimising bad pairs. True if cost reaches 0."""
    cur = _cost(adj, D)
    side0 = [v for v in range(len(adj)) if color[v] == 0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(side0)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(side0)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.1):
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0


def _lns(n, edges, d, D, deadline, rng, consider):
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4))
        if k >= cur_n:
            break
        kill = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in kill]
        remap = {v: i for i, v in enumerate(keep)}
        m = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u not in kill and v not in kill]
        adj = _to_sets(m, e2)
        color = _bipartition(m, adj)
        _fill(adj, color, d, rng)
        if _cost(adj, D) > 40:
            continue
        if not _anneal(adj, color, d, D, rng, 60, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.9 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
            consider(n1, e1)

    # Calibration cases already at the Moore bound return immediately.
    if D >= 2 and best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # New construction: Haar graphs of non-abelian groups, searched above the current best.
    if D >= 2 and d >= 2:
        lo = max(best_n // 2 + 1, d)
        hi = lib.moore_bound(d, D) // 2
        if lo <= hi:
            _group_search(d, D, lo, hi, start + 0.55 * time_limit, rng, consider)

    # Kill-repair-regrow search from the best valid graph found so far.
    if D >= 2 and time.monotonic() < deadline:
        _lns(best_n, best_e, d, D, start + 0.88 * time_limit, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
