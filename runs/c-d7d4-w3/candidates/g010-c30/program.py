import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# NEW construction: bipartite Haar-type lifts over finite groups.
#
# For a group G of order N and a connection set S (|S| = d), the graph on
# A = G and B = G with x ~ y iff x^{-1} y in S is d-regular and bipartite.
# Left multiplication is an automorphism that is transitive on each side, so
# the diameter is at most D iff BFS from the A-identity and from the
# B-identity reaches every vertex within D steps. That makes each evaluation
# two BFS passes, cheap enough for a local search over S.
# Groups are semidirect products Z_m x| Z_k, which include non-abelian groups.
# ----------------------------------------------------------------------------

def _sd_tables(m, k, r):
    """Multiplication table and inverse list of Z_m x|_r Z_k (element (a, b) coded as a*k + b)."""
    N = m * k
    idx = np.arange(N, dtype=np.int64)
    a = idx // k
    b = idx % k
    pw = np.array([pow(r, bb, m) for bb in range(k)], dtype=np.int64)
    # (a1, b1) * (a2, b2) = (a1 + r^b1 * a2, b1 + b2)
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    invs = np.argmax(M == 0, axis=1)
    return N, M.tolist(), invs.tolist()


def _group_list(N, rng):
    """Candidate groups of order N: cyclic, plus semidirect products Z_m x| Z_k with a few r."""
    out = [(N, 1, 1)]
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        rng.shuffle(rs)
        out.extend((m, k, r) for r in rs[:4])
    rng.shuffle(out)
    return out


def _haar_reach(N, M, S, Sinv, root, D):
    """Number of vertices within distance D of `root` (A-vertices 0..N-1, B-vertices N..2N-1)."""
    seen = bytearray(2 * N)
    seen[root] = 1
    frontier = [root]
    count = 1
    for _ in range(D):
        nxt = []
        for v in frontier:
            if v < N:
                row = M[v]
                for s in S:
                    w = N + row[s]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            else:
                row = M[v - N]
                for t in Sinv:
                    w = row[t]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
        count += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return count


def _haar_cost(N, M, invs, S, D):
    """Zero iff the Haar graph of S has diameter <= D (two BFS passes suffice by transitivity)."""
    Sinv = [invs[s] for s in S]
    a = _haar_reach(N, M, S, Sinv, 0, D)
    b = _haar_reach(N, M, S, Sinv, N, D)
    return 4 * N - a - b


def _anneal_haar(N, M, invs, S, D, rng, iters, deadline):
    """Single-element swap annealing on S. Returns (cost, S)."""
    S = list(S)
    cur = _haar_cost(N, M, invs, S, D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(len(S))
        g = rng.randrange(N)
        if g in S:
            continue
        old = S[i]
        S[i] = g
        c = _haar_cost(N, M, invs, S, D)
        if c <= cur or rng.random() < 0.02:
            cur = c
        else:
            S[i] = old
    return cur, S


def _group_phase(d, D, N_start, N_max, deadline, rng):
    """Ascend N, searching a valid group Haar graph of each order. Returns (N, M, S) of the last success."""
    best = None
    N = N_start
    while N <= N_max and time.monotonic() < deadline:
        tabs = [_sd_tables(m, k, r) for (m, k, r) in _group_list(N, rng)]
        found = None
        while found is None and tabs and time.monotonic() < deadline:
            for (_, M, invs) in tabs:
                if time.monotonic() >= deadline:
                    break
                S = rng.sample(range(N), d)
                c, S = _anneal_haar(N, M, invs, S, D, rng, 200, deadline)
                if c == 0:
                    found = (M, S)
                    break
        if found is None:
            break
        best = (N, found[0], found[1])
        N += 1
    return best


# ----------------------------------------------------------------------------
# Structured bases (from the parent).
# ----------------------------------------------------------------------------

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
    """W(q) incidence graph for the largest prime power q <= 16 with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers (from the parent).
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
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


def _cover_search(cands, ball, full, d, rng, iters, deadline):
    if not cands:
        return None
    k = min(d, len(cands))
    cur = rng.sample(cands, k)

    def cov(S):
        c = 0
        for s in S:
            c |= ball[s]
        return c

    cur_cov = cov(cur)
    cur_score = cur_cov.bit_count()
    for it in range(iters):
        if cur_cov == full:
            return cur
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        inn = rng.choice(cands)
        if inn in cur:
            continue
        trial = cur[:]
        trial[i] = inn
        t_cov = cov(trial)
        t_score = t_cov.bit_count()
        if t_score >= cur_score or rng.random() < 0.02:
            cur, cur_cov, cur_score = trial, t_cov, t_score
    return cur if cur_cov == full else None


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
            for attempt in range(60):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if not chosen and time.monotonic() < deadline:
                chosen = _cover_search(cands, ball, full, d, rng, 1500, deadline)
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
    """Greedily join deficient opposite-side vertices in random order. Keeps validity."""
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


def _cost(adj, D):
    """Number of vertex pairs at distance more than D."""
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
    """Bipartite double-edge switches minimising bad pairs. True if cost reaches 0."""
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
    """Kill-repair-regrow large-neighbourhood search from a valid graph."""
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
        if not _anneal(adj, color, d, D, rng, 150, deadline):
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


def _prune_redundant(n, edges, D, rng, deadline, max_tests):
    adj = _to_sets(n, edges)
    cand = list(edges)
    rng.shuffle(cand)
    tests = 0
    for u, v in cand:
        if tests >= max_tests or time.monotonic() > deadline:
            break
        if v not in adj[u]:
            continue
        tests += 1
        adj[u].discard(v)
        adj[v].discard(u)
        if _cost(adj, D) != 0:
            adj[u].add(v)
            adj[v].add(u)
    return [(a, b) for a in range(n) for b in adj[a] if a < b]


def _prune_regrow(n, edges, d, D, deadline, rng, consider):
    best_n, best_e = n, list(edges)
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        pe = _prune_redundant(cur_n, cur_e, D, rng, deadline, 160)
        n2, e2 = _grow(cur_n, pe, d, D, deadline, rng)
        consider(n2, e2)
        if n2 > best_n:
            best_n, best_e = n2, list(e2)
        if n2 >= cur_n - 1:
            cur_n, cur_e = n2, list(e2)
        elif n2 < best_n - 2 or rng.random() < 0.3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Driver. Budget T = 0.85 * time_limit.
#   G  group Haar lifts: ascend the order N, search S for each group (NEW)
#   A  structured base (W(q) or PG(2,q)) grown, as a second candidate
#   L  LNS from the best valid graph
#   P  prune and regrow from the best valid graph
# Every candidate passes lib.is_valid before it is kept. K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase G: group Haar lifts (new construction).
    if D >= 2 and d >= 2:
        try:
            N_max = max(d, lib.moore_bound(d, D) // 2)
            res = _group_phase(d, D, d, N_max, at(0.5), rng)
            if res is not None:
                N, M, S = res
                e = [(x, N + M[x][s]) for x in range(N) for s in S]
                consider(2 * N, e)
        except Exception:
            pass

    # Phase A: structured base, grown and kept as a second candidate.
    if D >= 3:
        try:
            base = _best_gq(d) if D >= 4 else None
            if base is None:
                base = _best_pg(d)
            if base is not None:
                n0, e0 = base
                consider(n0, e0)
                n1, e1 = _grow(n0, e0, d, D, at(0.6), rng)
                consider(n1, e1)
        except Exception:
            pass

    # Phase L: LNS from the best valid graph.
    if D >= 2 and time.monotonic() < at(0.8):
        try:
            _lns(best_n, best_e, d, D, at(0.8), rng, consider)
        except Exception:
            pass

    # Phase P: prune and regrow.
    if D >= 2 and time.monotonic() < at(1.0):
        try:
            _prune_regrow(best_n, best_e, d, D, at(1.0), rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
