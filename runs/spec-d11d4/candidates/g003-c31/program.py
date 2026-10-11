import math
import random
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions: projective plane (D = 3) and generalized quadrangle (D >= 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q); points are 0..P-1."""
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
    edges = []
    j = 0
    for i in range(P):
        x = pts[i]
        for k in range(i + 1, P):
            if (i, k) in covered:
                continue
            y = pts[k]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[t]), F.mul(b, y[t])) for t in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            for p in L:
                edges.append((p, P + j))
                for r in L:
                    if p < r:
                        covered.add((p, r))
            j += 1
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Graph utilities on adjacency lists and bitmasks.
# ----------------------------------------------------------------------------

def _adj_of(n, edges):
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


def _color(n, edges):
    return _bipartition(n, _adj_of(n, edges))


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
    """Number of unordered pairs at distance > D (zero means diameter <= D)."""
    ball = _balls(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


# ----------------------------------------------------------------------------
# Diameter-preserving growth: add a vertex whose neighbourhood covers the graph.
# ----------------------------------------------------------------------------

def _cover(cands, ball, full, k, rng, steps, deadline):
    """Find k candidate balls covering `full`: greedy seed, then swap local search."""
    if not cands:
        return None
    k = min(k, len(cands))
    covered, chosen, pool = 0, [], list(cands)
    while covered != full and len(chosen) < k and pool:
        best = max(pool, key=lambda s: (ball[s] & ~covered).bit_count())
        if (ball[best] & ~covered) == 0:
            break
        pool.remove(best)
        chosen.append(best)
        covered |= ball[best]
    if covered == full:
        return chosen
    S = chosen[:]
    while len(S) < k:
        c = rng.choice(cands)
        if c not in S:
            S.append(c)

    def uni(sel):
        u = 0
        for s in sel:
            u |= ball[s]
        return u

    cost = (full & ~uni(S)).bit_count()
    for step in range(steps):
        if cost == 0:
            return S
        if (step & 63) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        rest = S[:i] + S[i + 1:]
        miss = full & ~uni(rest)
        t = max(rng.sample(cands, min(40, len(cands))),
                key=lambda s: (ball[s] & miss).bit_count())
        if t in S:
            continue
        nc = (miss & ~ball[t]).bit_count()
        if nc <= cost or rng.random() < 0.02:
            S[i] = t
            cost = nc
    return S if cost == 0 else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Repeatedly add a vertex adjacent to a set of spare-degree vertices covering all within D-1."""
    edges = list(edges)
    adj = _adj_of(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            chosen = None
            for _ in range(6):
                if time.monotonic() >= deadline:
                    break
                chosen = _cover(cands, ball, full, d, rng, 1500, deadline)
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


# ----------------------------------------------------------------------------
# New family: insert a vertex by stealing edge slots, then repair the diameter by
# degree-preserving annealing (2-switches) and endpoint moves onto spare slots.
# ----------------------------------------------------------------------------

def _insert(n, col, E, d, rng):
    """Add vertex n on a random side, joined to d opposite-side vertices (freeing their slots)."""
    c = rng.randrange(2)
    opp = [v for v in range(n) if col[v] != c]
    chosen = rng.sample(opp, min(d, len(opp)))
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    drop = set()
    for w in chosen:
        if deg[w] >= d:
            cand = [i for i, (u, v) in enumerate(E) if (u == w or v == w) and i not in drop]
            i = rng.choice(cand)
            drop.add(i)
            deg[E[i][0]] -= 1
            deg[E[i][1]] -= 1
    E2 = [e for i, e in enumerate(E) if i not in drop]
    nv = n
    for w in chosen:
        E2.append((nv, w) if c == 0 else (w, nv))
    return n + 1, col + [c], E2


def _apply(E, es, deg, changes):
    """Replace E[k] by new tuples; returns the undo list."""
    undo = []
    for k, ne in changes:
        oe = E[k]
        undo.append((k, oe))
        es.discard(oe)
        deg[oe[0]] -= 1
        deg[oe[1]] -= 1
    for k, ne in changes:
        E[k] = ne
        es.add(ne)
        deg[ne[0]] += 1
        deg[ne[1]] += 1
    return undo


def _anneal(n, col, E, d, D, deadline, rng, steps):
    """Anneal bad-pair count to zero. Edits E in place; returns True if diameter <= D reached."""
    A = [v for v in range(n) if col[v] == 0]
    B = [v for v in range(n) if col[v] == 1]
    deg = [0] * n
    es = set(E)
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    cost = _bad(n, _adj_of(n, E), D)
    for step in range(steps):
        if cost == 0 or time.monotonic() >= deadline:
            break
        T = 1.5 * (0.03 ** (step / steps))
        i = rng.randrange(len(E))
        u, v = E[i]
        if rng.random() < 0.5:
            j = rng.randrange(len(E))
            u2, v2 = E[j]
            if u == u2 or v == v2:
                continue
            if (u, v2) in es or (u2, v) in es:
                continue
            ne = [(i, (u, v2)), (j, (u2, v))]
        elif rng.random() < 0.5:
            w = rng.choice(B)
            if deg[w] >= d or (u, w) in es:
                continue
            ne = [(i, (u, w))]
        else:
            w = rng.choice(A)
            if deg[w] >= d or (w, v) in es:
                continue
            ne = [(i, (w, v))]
        undo = _apply(E, es, deg, ne)
        c2 = _bad(n, _adj_of(n, E), D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _apply(E, es, deg, undo)
    return cost == 0


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, [tuple(x) for x in e]

    if D == 2:
        return best_n, best_e

    base = _best_pg(d) if D == 3 else _best_gq(d)
    if base is None:
        return best_n, best_e
    n0, e0 = base
    consider(n0, e0)

    # Calibration shortcut: the base is already the Moore-optimal graph.
    if D in (3, 4) and lib.is_prime_power(d - 1) and (D == 3 or d - 1 <= 9):
        return best_n, best_e

    col = [0] * (n0 // 2) + [1] * (n0 // 2)
    cur = (n0, col, [tuple(e) for e in e0])
    cover_done = False

    while time.monotonic() < deadline:
        n_c, col_c, E_c = cur

        if not cover_done:
            ncov, ecov = _extend_cover(n_c, E_c, d, D, deadline, rng)
            if ncov > n_c and lib.is_valid(ncov, ecov, d, D):
                consider(ncov, ecov)
                col2 = _color(ncov, ecov)
                cur = (ncov, col2, [(u, v) if col2[u] == 0 else (v, u) for u, v in ecov])
                continue
            cover_done = True

        n2, col2, E2 = _insert(n_c, col_c, E_c, d, rng)
        budget = min(deadline, time.monotonic() + 6.0)
        if _anneal(n2, col2, E2, d, D, budget, rng, 500):
            consider(n2, E2)
            cur = (n2, col2, E2)
            cover_done = False

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
