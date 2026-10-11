import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Base constructions: PG(2,q) for D = 3, and the generalized quadrangle W(q) for D = 4.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Point-line incidence graph of W(q): bipartite, diameter 4, degree q+1."""
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW IDEA: Haar graphs over finite groups with a diameter-4 local search.
#
# Let G be a finite group of order N and S a set of d elements. The Haar-type
# bipartite graph has vertices a_g, b_h (g, h in G) with a_g ~ b_{gs} for s in S.
# It is d-regular and bipartite by construction, with 2N vertices.
#
# Left multiplication is an automorphism, so distances reduce to three checks
# from the identity (a_1) and b_1:
#   E2a = {1} u S S^-1      (even walks of length <= 2 from a_1)
#   E2b = {1} u S^-1 S      (even walks of length <= 2 from b_1)
#   a-a pairs:  E2a * E2a must cover G
#   b-b pairs:  E2b * E2b must cover G
#   a-b pairs:  E2a * S    must cover G  (odd walks of length <= 3)
# The uncovered count is a cost. Simulated-annealing swaps of one element of S
# drive it to zero. Groups are semidirect products Z_m x| Z_k, with Z_N cyclic
# as a special case. Tables are built with numpy.
# ----------------------------------------------------------------------------

def _group_candidates(N):
    cands = [(N, 1, 1)]  # cyclic group Z_N
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        cands += [(m, k, r) for r in rs[:10]]
    return cands


def _group_table(m, k, r):
    """Multiplication table of Z_m x| Z_k; element (a, b) is coded a*k+b, identity is 0."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    A = x // k
    B = x % k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    pa = (A[:, None] + pw[B][:, None] * A[None, :]) % m
    pb = (B[:, None] + B[None, :]) % k
    return pa * k + pb


def _cost(S, table, inv, N):
    """Number of uncovered elements over the three coverage conditions."""
    invS = inv[S]
    zero = np.zeros(1, dtype=np.int64)
    e2a = np.unique(np.concatenate((zero, table[np.ix_(S, invS)].ravel())))
    e2b = np.unique(np.concatenate((zero, table[np.ix_(invS, S)].ravel())))
    c = 0
    mk = np.zeros(N, dtype=bool)
    mk[table[np.ix_(e2a, e2a)].ravel()] = True
    c += N - int(mk.sum())
    mk = np.zeros(N, dtype=bool)
    mk[table[np.ix_(e2b, e2b)].ravel()] = True
    c += N - int(mk.sum())
    mk = np.zeros(N, dtype=bool)
    mk[table[np.ix_(e2a, S)].ravel()] = True
    c += N - int(mk.sum())
    return c


def _local_search(N, d, table, inv, rng, deadline, steps=3000, rounds=4):
    for _ in range(rounds):
        if time.monotonic() >= deadline:
            return None
        S = rng.sample(range(N), d)
        cur = _cost(np.array(S, dtype=np.int64), table, inv, N)
        T = 0.5
        for it in range(steps):
            if cur == 0:
                return S
            if (it & 127) == 0 and time.monotonic() >= deadline:
                return None
            i = rng.randrange(d)
            g = rng.randrange(N)
            if g in S:
                continue
            old = S[i]
            S[i] = g
            c = _cost(np.array(S, dtype=np.int64), table, inv, N)
            if c <= cur or rng.random() < math.exp(-(c - cur) / T):
                cur = c
            else:
                S[i] = old
        if cur == 0:
            return S
    return None


def _haar_search(N, d, rng, deadline):
    if N < d or d < 2:
        return None
    cands = _group_candidates(N)
    while time.monotonic() < deadline:
        m, k, r = rng.choice(cands)
        table = _group_table(m, k, r)
        inv = np.argmax(table == 0, axis=1)
        S = _local_search(N, d, table, inv, rng, deadline)
        if S is not None:
            return table, S
    return None


def _haar_edges(N, table, S, d):
    Sarr = np.array(S, dtype=np.int64)
    G = np.arange(N, dtype=np.int64)
    H = table[G[:, None], Sarr[None, :]]          # shape (N, d)
    rows = np.repeat(G, d)
    cols = (N + H).ravel()
    return 2 * N, list(zip(rows.tolist(), cols.tolist()))


# ----------------------------------------------------------------------------
# Ball bitmasks and bipartition helpers (from the parent).
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


# ----------------------------------------------------------------------------
# Growth by cover (from the parent).
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
            thr = max(1, best_g - 1)
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _cover_ls(cands, ball, full, d, rng, steps, deadline):
    if not cands:
        return None
    k = min(d, len(cands))
    S = rng.sample(cands, k)
    in_s = set(S)

    def union(sel):
        u = 0
        for s in sel:
            u |= ball[s]
        return u

    cost = (full & ~union(S)).bit_count()
    for step in range(steps):
        if cost == 0:
            break
        if (step & 255) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        rest = S[:i] + S[i + 1:]
        miss = full & ~union(rest)
        best_t, best_g = None, -1
        for t in rng.sample(cands, min(40, len(cands))):
            if t in in_s:
                continue
            g = (ball[t] & miss).bit_count()
            if g > best_g:
                best_t, best_g = t, g
        if best_t is None:
            continue
        newcost = (miss & ~ball[best_t]).bit_count()
        if newcost <= cost or rng.random() < 0.02:
            in_s.discard(S[i])
            S[i] = best_t
            in_s.add(best_t)
            cost = newcost
    return S if cost == 0 else None


def _extend_cover(n, edges, d, D, deadline, rng):
    if D < 2:
        return n, edges
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
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(20):
                if time.monotonic() >= deadline:
                    break
                if attempt < 4:
                    chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                else:
                    chosen = _cover_ls(cands, ball, full, d, rng, 1500, deadline)
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
    """Join spare-degree vertices on opposite sides in random order (keeps bipartiteness)."""
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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
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
# Driver. Every candidate is validated with lib.is_valid before it can be kept.
# The fallback K_{d,d} is always valid for D >= 2.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.45 * time_limit, rng)
            consider(n2, e2)

    if D == 4 and d >= 3:
        # Binary search on the group order N for a Haar-type diameter-4 graph.
        # Each feasible N gives a 2N-vertex d-regular bipartite graph.
        lo = d
        hi = d * (1 + d * (d - 1))
        hdl = start + 0.7 * time_limit
        while lo < hi and time.monotonic() < hdl - 0.5:
            mid = (lo + hi + 1) // 2
            now = time.monotonic()
            budget = max(2.0, (hdl - now) * 0.4)
            res = _haar_search(mid, d, rng, min(hdl, now + budget))
            if res is None:
                hi = mid - 1
            else:
                table, S = res
                n2, e2 = _haar_edges(mid, table, S, d)
                consider(n2, e2)
                lo = mid

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            t = 0
            grow_deadline = start + 0.8 * time_limit
            while time.monotonic() < grow_deadline:
                n2, e2 = _grow(gq[0], gq[1], d, D, grow_deadline,
                               random.Random(seed * 131 + t))
                consider(n2, e2)
                t += 1
                if t >= 40:
                    break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
