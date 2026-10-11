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
# New construction: bipartite Cayley-type lifts over small groups.
#
# Vertices A_x and B_x for x in G (|G| = N). A_x ~ B_{x*s} for s in S, |S| = d.
# Left multiplication by h is an automorphism, so distances from A_e and B_e
# determine the diameter. Checking those two BFS trees (depth 4) is enough.
# Groups: Z_m x|_r Z_k, element (a,b) coded as a*k+b, multiplication built with numpy.
# Search: simulated annealing over S minimising the number of unreached vertices.
# ----------------------------------------------------------------------------

def _group_candidates(N):
    """Return (m, k, r) triples giving semidirect groups Z_m x|_r Z_k of order N (k=1 is cyclic)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        if k == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _cayley_table(m, k, r):
    """Return (MT, inv) with MT[x, y] the product of codes x, y, or None if the table is not a group."""
    N = m * k
    idx = np.arange(N, dtype=np.int64)
    a = idx // k
    b = idx % k
    pw = np.array([pow(r, bb, m) for bb in range(k)], dtype=np.int64)
    MT = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    if not np.all(MT[idx, inv] == 0):
        return None
    return MT, inv


def _missing(MT, Sa, Si, N):
    """Count vertices not reached within distance 4 from A_e and from B_e (0 means diameter <= 4)."""
    miss = 0
    for src in (0, 1):
        seen = [np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)]
        seen[src][0] = True
        fr = np.array([0], dtype=np.int64)
        side = src
        for _ in range(4):
            if fr.size == 0:
                break
            cols = Sa if side == 0 else Si
            nb = np.unique(MT[np.ix_(fr, cols)].ravel())
            tgt = 1 - side
            new = nb[~seen[tgt][nb]]
            seen[tgt][new] = True
            fr = new
            side = tgt
        miss += 2 * N - int(seen[0].sum()) - int(seen[1].sum())
    return miss


def _anneal(MT, inv, N, d, rng, deadline):
    """Search a connection set S of size d; return S with zero missing vertices, or None."""
    def val(S):
        Sa = np.array(S, dtype=np.int64)
        Si = inv[Sa]
        return _missing(MT, Sa, Si, N)

    S = rng.sample(range(N), d)
    cur = val(S)
    temp = 0.7
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        g = rng.randrange(N)
        if g in S:
            continue
        T = list(S)
        T[i] = g
        v = val(T)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = T, v
    return S if cur == 0 else None


def _cayley_search(d, D, best, deadline, rng):
    """Repeatedly try Cayley-type lifts of order just above the current record; return the best valid graph."""
    best_n = best[0]
    cache = {}
    while time.monotonic() < deadline - 0.5:
        N_lo = best_n // 2 + 1
        N = N_lo + int(rng.random() ** 2 * 30)
        if N < d:
            N = d
        if N not in cache:
            cands = _group_candidates(N)
            rng.shuffle(cands)
            cache[N] = cands
        cands = cache[N]
        if not cands:
            continue
        m, k, r = cands.pop()
        tab = _cayley_table(m, k, r)
        if tab is None:
            continue
        MT, inv = tab
        if N < d:
            continue
        slice_end = min(deadline, time.monotonic() + 2.0)
        S = _anneal(MT, inv, N, d, rng, slice_end)
        if S is None:
            continue
        n = 2 * N
        edges = [(x, N + int(MT[x, s])) for x in range(N) for s in S]
        if n > best_n and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_n = n
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + usable
    twin_deadline = t0 + 0.7 * usable
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

    # Twin construction on W(d-2): degree d, diameter 4 (baseline to beat).
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            consider(*_twin_graph(d - 2, twin_deadline, rng))
        except Exception:
            pass

    # Bold path: Cayley-type bipartite lifts over small semidirect groups.
    if D >= 4 and d >= 2:
        try:
            best = _cayley_search(d, D, best, deadline, rng)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
