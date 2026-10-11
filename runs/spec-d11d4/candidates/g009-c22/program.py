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
# Bold alternative: cyclic Haar graphs H(m, S) with |S| = d (bipartite,
# d-regular, 2m vertices). Diameter <= D holds iff every vertex is within
# distance D of a_0, because translations and the side-swapping automorphism
# a_i <-> b_{-i} make a_0 represent all pairs. A local search on S minimises
# the number of vertices unreached from a_0 within D steps.
# ----------------------------------------------------------------------------

def _haar_unreached(m, S, D):
    """Number of vertices of H(m, S) not within distance D of a_0 (both sides counted)."""
    seenA = np.zeros(m, dtype=bool)
    seenA[0] = True
    seenB = np.zeros(m, dtype=bool)
    fa = seenA.copy()
    fb = np.zeros(m, dtype=bool)
    for step in range(D):
        if step % 2 == 0:
            nb = np.zeros(m, dtype=bool)
            for s in S:
                nb |= np.roll(fa, s)
            nb &= ~seenB
            seenB |= nb
            fb = nb
        else:
            na = np.zeros(m, dtype=bool)
            for s in S:
                na |= np.roll(fb, -s)
            na &= ~seenA
            seenA |= na
            fa = na
    return int(m - seenA.sum()) + int(m - seenB.sum())


def _haar_search(m, k, D, deadline, rng):
    """Find k distinct residues S mod m with H(m, S) of diameter <= D, or return None."""
    while time.monotonic() < deadline:
        S = rng.sample(range(m), k)
        U = _haar_unreached(m, S, D)
        stall = 0
        while U > 0 and stall < 4000:
            if (stall & 255) == 0 and time.monotonic() >= deadline:
                return None
            i = rng.randrange(k)
            new = rng.randrange(m)
            if new in S:
                stall += 1
                continue
            T = list(S)
            T[i] = new
            V = _haar_unreached(m, T, D)
            if V < U:
                stall = 0
            else:
                stall += 1
            if V <= U or rng.random() < 0.01:
                S, U = T, V
        if U == 0:
            return S
    return None


def _haar_grow(d, D, start_n, deadline, rng):
    """Grow m upward from start_n/2 while searches succeed; return the best valid (n, edges) or None."""
    best = None
    m = start_n // 2 + 1
    while time.monotonic() < deadline:
        cap = min(deadline, time.monotonic() + 6.0)
        S = _haar_search(m, d, D, cap, rng)
        if S is None:
            break
        n, edges = lib.haar_graph(m, S)
        if n > start_n and lib.is_valid(n, edges, d, D):
            best = (n, edges)
        m += 1
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.7 * time_limit, time_limit - 12.0))
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

    # Twin construction on W(d-2) (degree d, diameter 4).
    # It gets about 60% of the budget; the remainder goes to the cyclic Haar search.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            twin_deadline = t0 + 0.6 * budget
            consider(*_twin_graph(d - 2, twin_deadline, rng))
        except Exception:
            pass

    # Bold path: cyclic Haar graph search for diameter-4 targets, seeded above the current best.
    if D >= 4 and d >= 6:
        try:
            found = _haar_grow(d, D, best[0], deadline, rng)
            if found is not None:
                consider(*found)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
