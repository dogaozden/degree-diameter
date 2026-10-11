import itertools
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
# Bold path: Haar graphs H(m, S) searched by local search (degree d, diameter 4).
#
# H(m, S): a_i ~ b_{i+s} for s in S. Translation i -> i+t is an automorphism,
# so diameter <= 4 holds iff the radius-4 balls around a_0 and b_0 cover
# everything. We minimise the number of uncovered vertices.
# ----------------------------------------------------------------------------

def _ball_unreached(m, S, side):
    """Number of vertices NOT within distance 4 of vertex 0 on the given side (0 = A, 1 = B)."""
    seenA = np.zeros(m, dtype=bool)
    seenB = np.zeros(m, dtype=bool)
    cur = np.array([0], dtype=np.int64)
    if side == 0:
        seenA[0] = True
    else:
        seenB[0] = True
    s = side
    for _ in range(4):
        if s == 0:
            nxt = ((cur[:, None] + S[None, :]) % m).ravel()
            seenB[nxt] = True
        else:
            nxt = ((cur[:, None] - S[None, :]) % m).ravel()
            seenA[nxt] = True
        cur = np.unique(nxt)
        s ^= 1
    return int((~seenA).sum() + (~seenB).sum())


def _haar_cost(m, S):
    return _ball_unreached(m, S, 0) + _ball_unreached(m, S, 1)


def _haar_search(d, m, deadline, rng):
    """Local search for S (|S| = d, 0 in S) with H(m, S) of diameter <= 4. Returns S as np array or None."""
    def random_set():
        return np.array([0] + rng.sample(range(1, m), d - 1), dtype=np.int64)

    S = random_set()
    c = _haar_cost(m, S)
    stall = 0
    while c > 0 and time.monotonic() < deadline:
        i = rng.randrange(1, d)
        inS = set(S.tolist())
        y = rng.randrange(1, m)
        while y in inS:
            y = rng.randrange(1, m)
        T = S.copy()
        T[i] = y
        ct = _haar_cost(m, T)
        if ct <= c:
            if ct < c:
                stall = 0
            else:
                stall += 1
            S, c = T, ct
        else:
            stall += 1
        if stall > 3000:
            S = random_set()
            c = _haar_cost(m, S)
            stall = 0
    return S if c == 0 else None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    # Projective plane incidence graph: degree d, diameter 3.
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Twins on W(d-2): degree d, diameter 4 (baseline record-level construction).
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            twin_deadline = t0 + 0.5 * budget
            consider(*_twin_graph(d - 2, twin_deadline, rng))
        except Exception:
            pass

    # Bold path: Haar-graph lifts of degree d searched for diameter 4 with
    # more than best[0] vertices (order 2m > best[0]).
    if D == 4 and d >= 4:
        try:
            m = best[0] // 2 + 1
            while True:
                now = time.monotonic()
                remaining = deadline - now
                if remaining < 0.5:
                    break
                slice_end = now + max(2.0, remaining / 3.0)
                slice_end = min(slice_end, deadline)
                S = _haar_search(d, m, slice_end, rng)
                if S is not None:
                    n_h, e_h = 2 * m, lib.haar_graph(m, [int(s) for s in S])[1]
                    consider(n_h, e_h)
                m += 1
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
