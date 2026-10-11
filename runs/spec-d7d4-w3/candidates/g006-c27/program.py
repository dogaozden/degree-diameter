import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Base constructions.
#   D = 3: incidence graphs of PG(2, q).
#   D >= 4: incidence graphs of the generalized quadrangle W(q), diameter 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q), a generalized quadrangle of diameter 4."""
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


def _bases(d, D):
    if d == 2:
        n = 2 * D
        return [(n, [(i, (i + 1) % n) for i in range(n)])]
    qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
    if D == 3:
        return [lib.projective_plane_incidence(q) for q in qs[:2]]
    if D >= 4:
        return [_gq_w(q) for q in qs if q <= 9][:2]
    return []


# ----------------------------------------------------------------------------
# Graph helpers.
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


def _ball_matrix(n, adj, r):
    """Boolean matrix B with B[s, x] = dist(s, x) <= r."""
    M = np.eye(n)
    for u in range(n):
        for v in adj[u]:
            M[u, v] = 1.0
    P = np.eye(n)
    for _ in range(r):
        P = ((P @ M) > 0).astype(np.float64)
    return P > 0


def _saturate(n, edges, d, rng):
    """Add edges between opposite-colour vertices with spare degree (keeps diameter)."""
    edges = list(edges)
    adj = _adjacency(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
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


def _remove_vertex(n, edges, x):
    """Delete vertex x; relabel the last vertex to x. Result is isomorphic to G - x."""
    last = n - 1

    def m(v):
        return x if v == last else v

    new = [(m(u), m(v)) for u, v in edges if u != x and v != x]
    return n - 1, new


# ----------------------------------------------------------------------------
# NEW HELPER: min-conflict local search for diameter-covering neighbourhoods.
#
# A new vertex v joined to a set S of same-side-opposite vertices keeps the
# diameter D iff the radius-(D-1) balls of S cover every vertex. We look for a
# cover of size <= d by a randomized greedy start followed by min-conflict
# swaps: pick an uncovered vertex, bring in a candidate covering it, and drop
# the member whose removal uncovers the fewest vertices (ties broken randomly).
# Worse moves are accepted with small probability to escape plateaus.
# ----------------------------------------------------------------------------

def _cover_ls(B, d, rng, iters, deadline):
    """B[i, x] = True if candidate i covers x. Return list of row indices covering all, or None."""
    nc, n = B.shape
    if nc == 0:
        return None
    Bi = B.astype(np.int32)
    inS = np.zeros(nc, dtype=bool)
    S = []
    cnt = np.zeros(n, dtype=np.int32)

    # Randomized greedy start.
    while len(S) < d:
        unc = cnt == 0
        if not unc.any():
            break
        gains = Bi[:, unc].sum(axis=1)
        gains[inS] = -1
        best = int(gains.max())
        if best <= 0:
            break
        thr = best - 1 if (best > 1 and rng.random() < 0.3) else best
        opts = np.flatnonzero(gains >= thr).tolist()
        c = rng.choice(opts)
        inS[c] = True
        S.append(c)
        cnt[:] += Bi[c]

    unc_now = int(np.count_nonzero(cnt == 0))
    best_unc = unc_now
    best_S = list(S)
    for _ in range(iters):
        if unc_now == 0 or time.monotonic() > deadline:
            break
        unc_idx = np.flatnonzero(cnt == 0)
        x = int(unc_idx[rng.randrange(len(unc_idx))])
        opts = np.flatnonzero((Bi[:, x] > 0) & ~inS).tolist()
        if not opts:
            continue
        c = rng.choice(opts)
        removed = -1
        if len(S) >= d:
            if rng.random() < 0.5:
                uniq = [int(np.count_nonzero((cnt == 1) & (Bi[s] > 0))) for s in S]
                mn = min(uniq)
                removed = rng.choice([s for s, u in zip(S, uniq) if u == mn])
            else:
                removed = rng.choice(S)
            inS[removed] = False
            S.remove(removed)
            cnt[:] -= Bi[removed]
        inS[c] = True
        S.append(c)
        cnt[:] += Bi[c]
        new_unc = int(np.count_nonzero(cnt == 0))
        if new_unc <= unc_now or rng.random() < 0.03:
            unc_now = new_unc
        else:
            inS[c] = False
            S.remove(c)
            cnt[:] -= Bi[c]
            if removed >= 0:
                inS[removed] = True
                S.append(removed)
                cnt[:] += Bi[removed]
        if unc_now < best_unc:
            best_unc = unc_now
            best_S = list(S)
    return best_S if best_unc == 0 else None


def _grow_ls(n, edges, d, D, deadline, rng):
    """Repeatedly add a vertex whose neighbourhood covers all radius-(D-1) balls."""
    edges = list(edges)
    while time.monotonic() < deadline:
        adj = _adjacency(n, edges)
        deg = [len(a) for a in adj]
        color = _bipartition(n, adj)
        ball = _ball_matrix(n, adj, D - 1)
        sides = [0, 1]
        rng.shuffle(sides)
        placed = False
        for t in sides:
            cands = [s for s in range(n) if color[s] == 1 - t and deg[s] < d]
            if not cands:
                continue
            B = ball[cands]
            chosen = None
            for _ in range(3):
                chosen = _cover_ls(B, d, rng, 400, deadline)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                for i in chosen:
                    edges.append((cands[i], v))
                placed = True
                break
        if not placed:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Twin blow-up: copy vertices with identical neighbourhoods (diameter-preserving).
# ----------------------------------------------------------------------------

def _twin_pass(n, edges, d, side, rng, tries):
    adj = _adjacency(n, edges)
    color = _bipartition(n, adj)
    cap = [d - len(a) for a in adj]
    cands = [v for v in range(n) if color[v] == side and adj[v]]
    if not cands:
        return n, edges
    best = []
    for _ in range(tries):
        rng.shuffle(cands)
        load = [0] * n
        chosen = []
        for v in cands:
            if all(load[u] < cap[u] for u in adj[v]):
                chosen.append(v)
                for u in adj[v]:
                    load[u] += 1
        if len(chosen) > len(best):
            best = chosen
    new_edges = list(edges)
    nn = n
    for v in best:
        for u in adj[v]:
            new_edges.append((u, nn))
        nn += 1
    return nn, new_edges


# ----------------------------------------------------------------------------
# Iterated local search: twin expansion or vertex excision, then cover regrowth.
# ----------------------------------------------------------------------------

def _improve(d, D, seed, deadline, bases, consider, st):
    rng = random.Random(seed * 1000003 + 17 * D + d)
    target = lib.moore_bound(d, D)
    cur = bases[0]
    while time.monotonic() < deadline and st["best"][0] < target:
        r = rng.random()
        if r < 0.1:
            cur = st["best"]
        elif r < 0.2:
            cur = rng.choice(bases)
        n0, e0 = cur
        if rng.random() < 0.5:
            n2, e2 = n0, list(e0)
            for side in (0, 1):
                n2, e2 = _twin_pass(n2, e2, d, side, rng, 6)
            n2, e2 = _grow_ls(n2, e2, d, D, deadline, rng)
        else:
            if n0 < 3:
                continue
            n2, e2 = _remove_vertex(n0, e0, rng.randrange(n0))
            if rng.random() < 0.3 and n2 > 2:
                n2, e2 = _remove_vertex(n2, e2, rng.randrange(n2))
            if not lib.within_diameter(n2, e2, D):
                e2 = _saturate(n2, e2, d, rng)
                if not lib.within_diameter(n2, e2, D):
                    continue
            n2, e2 = _grow_ls(n2, e2, d, D, deadline, rng)
        e2 = _saturate(n2, e2, d, rng)
        if n2 >= n0 or (n2 >= n0 - 1 and rng.random() < 0.1):
            cur = (n2, e2)
        if n2 > st["best"][0]:
            consider(n2, e2)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    st = {"best": lib.haar_graph(d, range(d))}  # K_{d,d}: valid fallback for D >= 2

    def consider(n, e):
        if n > st["best"][0] and lib.is_valid(n, e, d, D):
            st["best"] = (n, e)

    try:
        if st["best"][0] < lib.moore_bound(d, D):
            bases = _bases(d, D)
            for n, e in bases:
                consider(n, e)
            if bases and st["best"][0] < lib.moore_bound(d, D):
                _improve(d, D, seed, deadline, bases, consider, st)
    except Exception:
        pass

    n, e = st["best"]
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
