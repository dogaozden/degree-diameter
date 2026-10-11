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
# NEW helper: maximum independent set by iterated local search with
# (1,2)-swaps (Andrade-Resende-Werneck style), pure Python.
#
# A (1,2)-swap removes one solution vertex x and inserts two non-adjacent
# vertices u, w whose only solution neighbour is x. Perturbation forces a
# random outside vertex in; the best solution seen is kept and restored when
# the search drifts too far below it.
# ----------------------------------------------------------------------------

def _ils_mis(n, nbrs, deadline, rng):
    """Return a large independent set of the graph (n vertices, nbrs neighbour lists) found before deadline."""
    if n == 0:
        return []
    adjs = [set(a) for a in nbrs]
    inS = [False] * n
    tight = [0] * n
    S = set()

    def ins(v):
        inS[v] = True
        S.add(v)
        for w in nbrs[v]:
            tight[w] += 1

    def rem(v):
        inS[v] = False
        S.discard(v)
        for w in nbrs[v]:
            tight[w] -= 1

    def fill():
        free = [v for v in range(n) if not inS[v] and tight[v] == 0]
        rng.shuffle(free)
        for v in free:
            if not inS[v] and tight[v] == 0:
                ins(v)

    def two_improve():
        improved = True
        while improved:
            improved = False
            order = list(S)
            rng.shuffle(order)
            for x in order:
                if not inS[x]:
                    continue
                C = [u for u in nbrs[x] if tight[u] == 1]
                if len(C) < 2:
                    continue
                pair = None
                for i in range(len(C)):
                    au = adjs[C[i]]
                    for j in range(i + 1, len(C)):
                        if C[j] not in au:
                            pair = (C[i], C[j])
                            break
                    if pair:
                        break
                if pair:
                    rem(x)
                    ins(pair[0])
                    ins(pair[1])
                    fill()
                    improved = True

    fill()
    two_improve()
    best = list(S)
    bestsz = len(S)
    while time.monotonic() < deadline:
        cand = [v for v in range(n) if not inS[v]]
        if not cand:
            break
        v = rng.choice(cand)
        for w in list(nbrs[v]):
            if inS[w]:
                rem(w)
        ins(v)
        fill()
        two_improve()
        if len(S) > bestsz:
            best = list(S)
            bestsz = len(S)
        elif len(S) < bestsz - 1:
            for u in list(S):
                rem(u)
            for u in best:
                ins(u)
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
#
# Point-side extras x_p (p in I, I a partial ovoid) join the lines through p;
# line-side extras y_j (j in J, J a partial spread) join the points on j.
# Independence of I and J keeps every line/point within degree q+2.
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
    I = _ils_mis(P, [sorted(s) for s in padj], mid, rng)
    J = _ils_mis(L, [sorted(s) for s in ladj], deadline, rng)

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
# Greedy set-cover vertex extension for diameter 4.
# ----------------------------------------------------------------------------

def _ball3(n, adj):
    """Return per-vertex bitmasks of all vertices within distance 3."""
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _extend(n, edges, d, deadline, rng):
    """Greedily add vertices while keeping max degree d and diameter 4; return (n, edges)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if color[w] == -1:
                    color[w] = 1 - color[u]
                    stack.append(w)

    fails = 0
    while time.monotonic() < deadline and fails < 3000:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline and fails < 3000:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            s0 = rng.choice(spare)
            pool = [v for v in spare if color[v] == color[s0] and v != s0]
            S = [s0]
            unc = full & ~reach[s0]
            while unc and len(S) < d and pool:
                best, bv = 0, -1
                for v in pool:
                    g = (reach[v] & unc).bit_count()
                    if g > best:
                        best, bv = g, v
                if bv < 0:
                    break
                S.append(bv)
                unc &= ~reach[bv]
                pool.remove(bv)
            if unc:
                fails += 1
                continue
            x = n
            n += 1
            for s in S:
                edges.append((s, x))
                adj[s].append(x)
            adj.append(list(S))
            color.append(1 - color[s0])
            fails = 0
            grown = True
            break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Random Haar graphs H(Z_m, S) with |S| = d (cheap fallback / small cases).
# ----------------------------------------------------------------------------

def _haar_ok(m, S, D):
    """True if the Haar graph on Z_m with connection set S has diameter <= D."""
    A = np.zeros(m, dtype=bool)
    A[0] = True
    B = np.zeros(m, dtype=bool)
    negS = [(-s) % m for s in S]
    for step in range(D):
        Y = np.zeros(m, dtype=bool)
        if step % 2 == 0:
            for s in S:
                Y |= np.roll(A, s)
            B |= Y
        else:
            for t in negS:
                Y |= np.roll(B, t)
            A |= Y
    return bool(A.all() and B.all())


def _haar_search(d, D, m_hi, rng, deadline, trials_per):
    """Binary search for the largest m with a working random Haar graph; return (m, S)."""
    lo, hi = d, max(d, m_hi)
    best = (d, list(range(d)))
    while lo < hi and time.monotonic() < deadline:
        mid = (lo + hi + 1) // 2
        found = None
        for _ in range(trials_per):
            if time.monotonic() >= deadline:
                break
            S = rng.sample(range(mid), d)
            if _haar_ok(mid, S, D):
                found = S
                break
        if found is not None:
            best = (mid, found)
            lo = mid
        else:
            hi = mid - 1
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 6.0))
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

    # Phase 1: short random Haar search (rarely competitive for large d, so keep it small).
    try:
        m_hi = max(d, lib._moore_bound(d, D) // 2)
        m, S = _haar_search(d, D, m_hi, rng, t0 + 0.1 * budget, 800)
        consider(*lib.haar_graph(m, S))
    except Exception:
        pass

    # Phase 2: algebraic constructions.
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Phase 3: twin construction on W(q) with ILS-searched partial ovoid / spread.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            now = time.monotonic()
            twin_deadline = now + 0.75 * (deadline - now)
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
