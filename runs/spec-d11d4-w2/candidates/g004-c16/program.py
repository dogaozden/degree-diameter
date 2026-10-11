import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) as a point/line list (table-based, pure Python).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Return (P, lines): points of W(q) indexed 0..P-1 and each totally isotropic line as a sorted point list."""
    F = lib.GF(q)
    mul = F.mul_table.tolist()
    add = F.add_table.tolist()
    neg = [next(b for b in range(q) if add[a][b] == 0) for a in range(q)]
    inv = [0] * q
    for a in range(1, q):
        inv[a] = next(b for b in range(1, q) if mul[a][b] == 1)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        ic = inv[c]
        return tuple(mul[ic][x] for x in v)

    def form(x, y):
        t = add[mul[x[0]][y[1]]][neg[mul[x[1]][y[0]]]]
        u = add[mul[x[2]][y[3]]][neg[mul[x[3]][y[2]]]]
        return add[t][u]

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i * P + j) in covered:
                continue
            y = pts[j]
            if form(x, y):
                continue
            Lset = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(add[mul[a][x[k]]][mul[b][y[k]]] for k in range(4))
                    if any(v):
                        Lset.add(index[norm(v)])
            Ls = sorted(Lset)
            lines.append(Ls)
            for p in Ls:
                for r in Ls:
                    if p < r:
                        covered.add(p * P + r)
    return P, lines


def _gq_incidence(q):
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1; degree q+1, diameter 4."""
    P, lines = _gq_w(q)
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Maximum independent set by k-fixed tabu search (pure Python).
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    inS = [False] * n
    c = [0] * n
    S = []

    def add(v):
        inS[v] = True
        S.append(v)
        for w in adj[v]:
            c[w] += 1

    def remove(u):
        inS[u] = False
        S.remove(u)
        for w in adj[u]:
            c[w] -= 1

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if c[v] == 0:
            add(v)
    best = list(S)
    tab_add = [0] * n
    tab_rem = [0] * n
    it = 0
    stuck = 0
    while time.monotonic() < deadline:
        it += 1
        cost = sum(c[v] for v in S)
        if cost == 0:
            if len(S) > len(best):
                best = list(S)
                stuck = 0
            cands = [v for v in range(n) if not inS[v] and tab_add[v] <= it] \
                or [v for v in range(n) if not inS[v]]
            if not cands:
                break
            mn = min(c[v] for v in cands)
            add(rng.choice([v for v in cands if c[v] == mn]))
            continue
        stuck += 1
        if stuck > 3000:
            for v in list(S):
                remove(v)
            for v in best:
                add(v)
            stuck = 0
            continue
        ok = [u for u in S if tab_rem[u] <= it] or list(S)
        mx = max(c[u] for u in ok)
        u = rng.choice([x for x in ok if c[x] == mx])
        remove(u)
        tab_add[u] = it + rng.randint(5, 15)
        cands = [v for v in range(n) if not inS[v] and tab_add[v] <= it] \
            or [v for v in range(n) if not inS[v]]
        mn = min(c[v] for v in cands)
        v = rng.choice([x for x in cands if c[x] == mn])
        add(v)
        tab_rem[v] = it + rng.randint(5, 15)
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
# ----------------------------------------------------------------------------

def _twin_graph(q, deadline, rng):
    P, lines = _gq_w(q)
    L = len(lines)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    padj = [set() for _ in range(P)]
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)
    ladj = [set() for _ in range(L)]
    for p in range(P):
        for a in pl[p]:
            for b in pl[p]:
                if a != b:
                    ladj[a].add(b)

    now = time.monotonic()
    mid = now + (deadline - now) / 2.0
    I = _mis(P, [sorted(s) for s in padj], mid, rng)
    J = _mis(L, [sorted(s) for s in ladj], deadline, rng)

    edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    n = P + L
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        n += 1
    for j in J:
        for p in lines[j]:
            edges.append((p, n))
        n += 1
    return n, edges


# ----------------------------------------------------------------------------
# NEW CONSTRUCTION: ball-cover augmentation.
#
# Given a valid graph G (max degree d, diameter <= D, bipartite), a new vertex y
# joined to a set B of vertices all on one side keeps everything valid when
#   union over b in B of Ball_{D-1}(b) = V(G).
# Proof: dist(y, w) = 1 + min_b dist(b, w) <= D, and old distances can only
# shrink. The new vertex lies on the opposite side, so bipartiteness is kept.
# So we repeatedly pick a side, run randomized greedy set cover over the
# vertices with spare degree on that side (sets = radius-(D-1) balls held as
# bitmasks), and attach y if the cover uses at most d sets. Balls are recomputed
# after each success.
# ----------------------------------------------------------------------------

def _ball_masks(n, adj, R):
    """Bitmask per vertex of all vertices within distance R."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _two_color(n, adj):
    """Bipartition colouring as a list, or None if the graph has an odd cycle."""
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


def _augment(n, edges, d, D, deadline, rng):
    """Greedily attach extra vertices whose neighbourhoods radius-(D-1)-cover the graph; return (n, edges)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _two_color(n, adj)
    if color is None:
        return n, list(edges)
    edges = list(edges)
    deg = [len(a) for a in adj]
    R = D - 1
    balls = None
    full = 0
    fails = 0
    while fails < 200 and time.monotonic() < deadline:
        if balls is None:
            balls = _ball_masks(n, adj, R)
            full = (1 << n) - 1
        side = rng.randrange(2)
        pool = [v for v in range(n) if color[v] == side and deg[v] < d]
        if not pool:
            fails += 1
            continue
        covered = 0
        chosen = []
        used = set()
        for _ in range(d):
            rem = full ^ covered
            if rem == 0:
                break
            scored = []
            for v in pool:
                if v in used:
                    continue
                g = (balls[v] & rem).bit_count()
                if g:
                    scored.append((g, v))
            if not scored:
                break
            top = max(g for g, _ in scored)
            thr = top - 1 if rng.random() < 0.25 else top  # mild randomisation
            pick = rng.choice([v for g, v in scored if g >= thr])
            used.add(pick)
            chosen.append(pick)
            covered |= balls[pick]
        if chosen and covered == full:
            y = n
            color.append(1 - side)
            adj.append(list(chosen))
            deg.append(len(chosen))
            for b in chosen:
                adj[b].append(y)
                deg[b] += 1
                edges.append((b, y))
            n += 1
            balls = None
            fails = 0
        else:
            fails += 1
    return n, edges


# ----------------------------------------------------------------------------
# Bi-Cayley (Haar-type) graphs over small groups with optimized connection sets.
# ----------------------------------------------------------------------------

def _group_options(N):
    """Return (m, k, r) choices giving groups of order N: cyclic Z_N and Z_m x|_r Z_k."""
    opts = [(N, 1, 1)]
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _mul_table(m, k, r):
    """Full multiplication table of Z_m x|_r Z_k with element (a, b) coded as a*k+b (identity is 0)."""
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(m * k, dtype=np.int64)
    a = (x // k)[:, None]
    b = (x % k)[:, None]
    c = (x // k)[None, :]
    dd = (x % k)[None, :]
    na = (a + pw[b] * c) % m
    nb = (b + dd) % k
    return na * k + nb


def _sa_search(N, MT, inv, d, M3, deadline, rng):
    """Simulated annealing over connection sets S; return (True, S) on full coverage, else (False, best S)."""

    def cost(S):
        Q = MT[S[:, None], inv[S][None, :]]
        W = MT[Q[:, :, None], S[None, None, :]]
        cov = np.zeros(N, dtype=bool)
        cov[W[M3]] = True
        cov[S] = True
        return N - int(cov.sum())

    S = np.array(rng.sample(range(N), d), dtype=np.int64)
    cur = cost(S)
    best = cur
    bestS = S.copy()
    t_start = time.monotonic()
    span = max(deadline - t_start, 1e-6)
    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t_start) / span
        T = 1.5 * (1.0 - frac) + 0.1
        p = rng.randrange(d)
        inS = set(S.tolist())
        new = rng.randrange(N)
        while new in inS:
            new = rng.randrange(N)
        S2 = S.copy()
        S2[p] = new
        c2 = cost(S2)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            S = S2
            cur = c2
            if cur < best:
                best = cur
                bestS = S.copy()
    return cur == 0, bestS


def _find_connection_set(N, d, deadline, rng):
    """Try random groups of order N with SA on S until deadline; return (m, k, r, S) or None."""
    if N < d + 1:
        return None
    opts = _group_options(N)
    M3 = (~np.eye(d, dtype=bool))[:, :, None] & (~np.eye(d, dtype=bool))[None, :, :]
    while time.monotonic() < deadline:
        m, k, r = rng.choice(opts)
        MT = _mul_table(m, k, r)
        inv = np.argmax(MT == 0, axis=1).astype(np.int64)
        sub_deadline = min(deadline, time.monotonic() + 0.7)
        ok, S = _sa_search(N, MT, inv, d, M3, sub_deadline, rng)
        if ok:
            return (m, k, r, [int(s) for s in S])
    return None


def _bicayley(d, D, deadline, rng):
    """Bisection over group order N for the largest bi-Cayley graph of diameter <= D; return (n, edges) or None."""
    if D != 4 or d < 3:
        return None
    moore = lib._moore_bound(d, D)
    lo, hi = max(d + 1, 2), moore // 2
    best = None
    while lo <= hi and time.monotonic() < deadline:
        N = (lo + hi + 1) // 2
        slot_end = min(deadline, time.monotonic() + 2.5)
        res = _find_connection_set(N, d, slot_end, rng)
        if res is not None:
            best = (N, res)
            lo = N + 1
        else:
            hi = N - 1
    if best is None:
        return None
    N, (m, k, r, S) = best
    order, mul = lib.semidirect_group(m, k, r)
    darts = [(0, 1, g) for g in S]
    return lib.group_lift(2, darts, order, mul)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    rng = random.Random(seed)

    def at(frac):
        return t0 + frac * budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, list(edges))

    def consider_aug(n, edges, dl):
        consider(n, edges)
        try:
            n2, e2 = _augment(n, edges, d, D, dl, random.Random(rng.random()))
            consider(n2, e2)
        except Exception:
            pass

    # Projective plane incidence graph: degree d, diameter 3 (Moore graph, no spare slots).
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # Generalized quadrangle W(d-1): degree d-1 with one spare slot per vertex, diameter 4.
    # Greedy ball-cover augmentation then adds vertices using the spare slots.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            n, e = _gq_incidence(d - 1)
            consider_aug(n, e, at(0.40))
        except Exception:
            pass

    # Twin construction on W(d-2) (degree d, diameter 4), then augmentation.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n, e = _twin_graph(d - 2, at(0.65), rng)
            consider_aug(n, e, at(0.88))
        except Exception:
            pass

    # Bi-Cayley graphs with whatever time is left.
    if D >= 4 and at(0.95) - time.monotonic() > 3.0:
        try:
            res = _bicayley(d, D, at(0.95), rng)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
