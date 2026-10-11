import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Fast diameter-deficiency count: number of unordered pairs at distance > D.
# ----------------------------------------------------------------------------

def _bad_pairs(n, E, D):
    adj = [[] for _ in range(n)]
    for x, y in E:
        adj[x].append(y)
        adj[y].append(x)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q); diameter 4, degree q+1."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _state(n, edges):
    """Normalize edges to (side0, side1) tuples using a BFS 2-colouring."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        st = [s]
        while st:
            u = st.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    st.append(v)
    return [(u, v) if color[u] == 0 else (v, u) for u, v in edges]


# ----------------------------------------------------------------------------
# Growth: add two vertices (one per side), each of degree d, by rewiring
# existing edges (degree-preserving for old vertices).
# ----------------------------------------------------------------------------

def _add_pair(n, E, d, rng):
    E = list(E)
    a, b = n, n + 1
    old = n
    ys, xs = set(), set()
    k = 0
    tries = 0
    m = len(E)
    while k < d:
        tries += 1
        if tries > 200000:
            return None
        i = rng.randrange(m)
        x, y = E[i]
        if x >= old or y >= old:
            continue
        if y in ys or x in xs:
            continue
        ys.add(y)
        xs.add(x)
        E[i] = (a, y)      # remove (x, y), add (a, y)
        E.append((x, b))   # and add (x, b)
        k += 1
    return n + 2, E


# ----------------------------------------------------------------------------
# Repair: simulated annealing over degree-preserving double-edge swaps,
# minimizing the number of pairs at distance > D.
# ----------------------------------------------------------------------------

def _repair(n, E, D, deadline, rng):
    """Modify E in place; return E if diameter <= D is reached before deadline, else None."""
    m = len(E)
    Eset = set(E)
    cost = _bad_pairs(n, E, D)
    T = 0.6
    while cost > 0:
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        x, y = E[i]
        z, w = E[j]
        if x == z or y == w:
            continue
        if (x, w) in Eset or (z, y) in Eset:
            continue
        E[i] = (x, w)
        E[j] = (z, y)
        c2 = _bad_pairs(n, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            Eset.discard((x, y))
            Eset.discard((z, w))
            Eset.add((x, w))
            Eset.add((z, y))
            cost = c2
        else:
            E[i] = (x, y)
            E[j] = (z, w)
        T = max(0.2, T * 0.9995)
    return E


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
    if D >= 4:
        for q in range(min(d - 1, 5), 1, -1):
            if lib.is_prime_power(q):
                consider(*_gq_w(q))
                break

    # Growth phase: only if the Moore bound is not already attained.
    if D >= 3 and best_n >= 4 and best_n < lib._moore_bound(d, D):
        rng = random.Random(seed * 7919 + d * 131 + D)
        cur_n = best_n
        cur_E = _state(best_n, best_e)
        slice_len = max(2.0, 0.1 * time_limit)
        while time.monotonic() < deadline:
            cand = _add_pair(cur_n, cur_E, d, rng)
            if cand is None:
                continue
            tn, tE = cand
            end = min(deadline, time.monotonic() + slice_len)
            res = _repair(tn, tE, D, end, rng)
            if res is not None and lib.is_valid(tn, res, d, D):
                cur_n, cur_E = tn, res
                consider(tn, res)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, list(best_e)
