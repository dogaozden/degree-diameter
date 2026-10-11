"""Growth program for bipartite (d, D) graphs.

New in this version: "2-switch simulated annealing insertion".
To add one vertex v to a valid graph G, we form G + v with no edges on v and
anneal the whole graph on the number of bad pairs (pairs at distance > D).
Moves are (a) steal-attach: join v to a random opposite-side t, first dropping
one edge of v or t if either is full; and (b) degree-preserving 2-switches
(a-b, c-e -> a-e, c-b) that move spare capacity around the graph, so repairs
can reach far from v. Free edge additions (saturation) never increase bad
pairs, so they run periodically during the anneal. Every accepted result is
verified with lib.is_valid.

Growth alternates twin packing (copies of a vertex with the same neighbourhood,
which keeps diameter) with this annealed insertion.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Base graphs.
# ----------------------------------------------------------------------------

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


def _bases(d, D):
    out = []
    if D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            out.append(lib.projective_plane_incidence(q))
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                out.append(lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass
    elif D >= 4:
        qs = [q for q in range(min(d - 1, 7), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            out.append(_gq_w(q))
    return out


# ----------------------------------------------------------------------------
# Helpers on edge lists.
# ----------------------------------------------------------------------------

def _adj(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _colors(n, adj):
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
    return [c if c >= 0 else 0 for c in color]


# ----------------------------------------------------------------------------
# Twin packing: copy vertices with identical neighbourhoods. Copies keep
# distances (d(w', x) = d(w, x)), so the diameter bound is preserved.
# ----------------------------------------------------------------------------

def _twin_side(n, edges, d, side, rng, tries):
    adj = _adj(n, edges)
    color = _colors(n, adj)
    deg = [len(a) for a in adj]
    cands = [v for v in range(n) if color[v] == side and adj[v]]
    if not cands:
        return n, edges
    best = []
    for _ in range(tries):
        order = cands[:]
        rng.shuffle(order)
        cap = [d - x for x in deg]
        chosen = []
        for v in order:
            if all(cap[u] >= 1 for u in adj[v]):
                chosen.append(v)
                for u in adj[v]:
                    cap[u] -= 1
        if len(chosen) > len(best):
            best = chosen
    if not best:
        return n, edges
    new = list(edges)
    nn = n
    for v in best:
        for u in adj[v]:
            new.append((u, nn))
        nn += 1
    return nn, new


# ----------------------------------------------------------------------------
# Matrix-based annealed insertion (the new construction step).
# ----------------------------------------------------------------------------

def _bad_count(A, D):
    """Number of unordered pairs at distance > D, via boolean powers of (I + A)."""
    N = A.shape[0]
    M = A.copy()
    np.fill_diagonal(M, 1.0)
    R = M
    for _ in range(D - 1):
        R = ((R @ M) > 0).astype(np.float32)
    return (N * N - int(np.count_nonzero(R))) // 2


def _saturate(A, color, deg, d, rng):
    """Add edges between non-adjacent opposite-side vertices with spare degree (never hurts diameter)."""
    N = len(deg)
    L = [x for x in range(N) if color[x] == 0 and deg[x] < d]
    R = [x for x in range(N) if color[x] == 1 and deg[x] < d]
    rng.shuffle(L)
    rng.shuffle(R)
    for a in L:
        if deg[a] >= d:
            continue
        for b in R:
            if deg[a] >= d:
                break
            if deg[b] < d and A[a, b] == 0:
                A[a, b] = 1.0
                A[b, a] = 1.0
                deg[a] += 1
                deg[b] += 1


def _apply(A, deg, ops):
    """ops: list of (kind, a, b); kind 1 = add edge, 0 = remove edge."""
    for kind, a, b in ops:
        val = 1.0 if kind == 1 else 0.0
        A[a, b] = val
        A[b, a] = val
        step = 1 if kind == 1 else -1
        deg[a] += step
        deg[b] += step


def _steal_ops(A, deg, d, v, opp, rng):
    """Attach the new vertex v to a random opposite-side t, dropping one edge of each endpoint that is full."""
    t = opp[rng.randrange(len(opp))]
    if A[v, t] != 0:
        return None
    ops = []
    if deg[v] >= d:
        nb = np.flatnonzero(A[v])
        s = int(nb[rng.randrange(len(nb))])
        ops.append((0, v, s))
    if deg[t] >= d:
        nb = np.flatnonzero(A[t])
        u = int(nb[rng.randrange(len(nb))])
        ops.append((0, t, u))
    ops.append((1, v, t))
    return ops


def _switch_ops(A, color, deg, N, rng):
    """Degree-preserving 2-switch on two left-side vertices: a-b, c-e -> a-e, c-b."""
    lefts = [x for x in range(N) if color[x] == 0 and deg[x] > 0]
    if len(lefts) < 2:
        return None
    a = lefts[rng.randrange(len(lefts))]
    c = lefts[rng.randrange(len(lefts))]
    if a == c:
        return None
    nb_a = np.flatnonzero(A[a])
    b = int(nb_a[rng.randrange(len(nb_a))])
    nb_c = np.flatnonzero(A[c])
    e = int(nb_c[rng.randrange(len(nb_c))])
    if A[a, e] != 0 or A[c, b] != 0:
        return None
    return [(0, a, b), (0, c, e), (1, a, e), (1, c, b)]


def _insert_anneal(A, color, deg, d, D, iters, deadline, rng):
    """Anneal the last vertex's neighbourhood plus 2-switches on bad-pair count. True when bad == 0."""
    N = A.shape[0]
    v = N - 1
    opp = [x for x in range(N) if color[x] != color[v]]
    cur = _bad_count(A, D)
    T0 = 1.5
    for it in range(iters):
        if cur == 0:
            return True
        if time.monotonic() > deadline:
            break
        if it % 64 == 63:
            _saturate(A, color, deg, d, rng)
            cur = _bad_count(A, D)
            continue
        T = max(0.08, T0 * (0.9995 ** it))
        if rng.random() < 0.5:
            ops = _steal_ops(A, deg, d, v, opp, rng)
        else:
            ops = _switch_ops(A, color, deg, N, rng)
        if ops is None:
            continue
        _apply(A, deg, ops)
        new = _bad_count(A, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            _apply(A, deg, [(1 - k, a, b) for k, a, b in reversed(ops)])
    return cur == 0


def _grow(n, edges, d, D, deadline, rng):
    """Repeatedly insert one vertex by annealing; stop after repeated failures or at the deadline."""
    cn, ce = n, list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 4:
        A = np.zeros((cn + 1, cn + 1), dtype=np.float32)
        for u, v in ce:
            A[u, v] = 1.0
            A[v, u] = 1.0
        deg = [int(x) for x in A[:cn, :cn].sum(axis=1)]
        color = _colors(cn, _adj(cn, ce))
        deg.append(0)
        color.append(rng.randrange(2))
        ok = _insert_anneal(A, color, deg, d, D, 3000,
                            min(deadline, time.monotonic() + 8.0), rng)
        if ok:
            _saturate(A, color, deg, d, rng)
            ne = [(int(a), int(b)) for a, b in np.argwhere(np.triu(A, 1) > 0)]
            if lib.is_valid(cn + 1, ne, d, D):
                cn, ce = cn + 1, ne
                fails = 0
                continue
        fails += 1
    return cn, ce


def _expand(n, edges, d, D, deadline, rng):
    """Alternate twin packing (both sides) with annealed growth until stale or out of time."""
    cur = (n, edges)
    stale = 0
    while time.monotonic() < deadline and stale < 3:
        n0 = cur[0]
        for side in (0, 1):
            if time.monotonic() >= deadline:
                break
            tn, te = _twin_side(cur[0], cur[1], d, side, rng, 20)
            if tn > cur[0] and lib.is_valid(tn, te, d, D):
                cur = (tn, te)
        gn, ge = _grow(cur[0], cur[1], d, D, deadline, rng)
        cur = (gn, ge)
        stale = stale + 1 if cur[0] == n0 else 0
    return cur


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(0.3, min(0.85 * time_limit, time_limit - 2.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    valid_bases = []
    for n, e in _bases(d, D):
        if lib.is_valid(n, e, d, D):
            valid_bases.append((n, e))
    valid_bases.sort(key=lambda x: -x[0])
    for n, e in valid_bases:
        if n > best[0]:
            best = (n, e)

    # Calibration shortcut: already at the Moore bound.
    if best[0] >= lib._moore_bound(d, D):
        return best

    starts = valid_bases[:2] if valid_bases else [best]
    fracs = [0.7, 0.3] if len(starts) == 2 else [1.0]
    cursor = time.monotonic()
    total = max(0.0, deadline - cursor)
    for (n, e), f in zip(starts, fracs):
        end = cursor + f * total
        cand = _expand(n, e, d, D, end, rng)
        if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
        cursor = end

    return best
