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
# NEW: iterated local search for maximum independent set (ARW-style):
# (1,2)-swaps plus random forced insertions, with occasional restore of the best.
# ----------------------------------------------------------------------------

def _ils_mis(n, adjs, deadline, rng):
    """Return a large independent set of the graph (n vertices, adjs neighbour lists) found before deadline."""
    aset = [set(a) for a in adjs]
    sol = set()
    t = [0] * n  # number of solution neighbours of each vertex

    def ins(v):
        sol.add(v)
        for w in adjs[v]:
            t[w] += 1

    def rem(v):
        sol.discard(v)
        for w in adjs[v]:
            t[w] -= 1

    def fill(cands):
        for v in cands:
            if v not in sol and t[v] == 0:
                ins(v)

    order = list(range(n))
    rng.shuffle(order)
    fill(order)
    best = set(sol)
    while time.monotonic() < deadline:
        improved = False
        xs = list(sol)
        rng.shuffle(xs)
        for x in xs:
            if x not in sol:
                continue
            L = [v for v in adjs[x] if t[v] == 1]
            if len(L) < 2:
                continue
            rng.shuffle(L)
            pair = None
            for i in range(len(L)):
                u = L[i]
                for j in range(i + 1, len(L)):
                    w = L[j]
                    if w not in aset[u]:
                        pair = (u, w)
                        break
                if pair is not None:
                    break
            if pair is None:
                continue
            rem(x)
            ins(pair[0])
            ins(pair[1])
            fill(L)
            improved = True
            if len(sol) > len(best):
                best = set(sol)
        if not improved:
            v = rng.randrange(n)
            if v not in sol:
                for w in adjs[v]:
                    if w in sol:
                        rem(w)
                ins(v)
                fill(order)
        if len(sol) + 3 < len(best) and rng.random() < 0.05:
            for v in list(sol):
                rem(v)
            fill(list(best))
        if len(sol) > len(best):
            best = set(sol)
    return sorted(best)


# ----------------------------------------------------------------------------
# NEW twin construction on W(q), degree q+2 (for d = q+2, D = 4).
# Points get an independent set I of new line-type vertices, lines get an
# independent set J of new point-type vertices; I-vertices and J-vertices are
# then matched to each other to use spare degree. Diameter 4 holds for any
# independent I and J (generalized quadrangle axioms).
# ----------------------------------------------------------------------------

def _twin2(q, deadline, rng):
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
    span = max(0.0, deadline - now)
    I = _ils_mis(P, [sorted(s) for s in padj], now + 0.4 * span, rng)
    J = _ils_mis(L, [sorted(s) for s in ladj], now + 0.8 * span, rng)

    edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    n = P + L
    Ivs = []
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        Ivs.append(n)
        n += 1
    Jvs = []
    for j in J:
        for p in lines[j]:
            edges.append((p, n))
        Jvs.append(n)
        n += 1
    # Use the spare degree (one per I- and J-vertex): match them up.
    # I-vertices lie on the point side, J-vertices on the line side, so this stays bipartite.
    for a, b in zip(Ivs, Jvs):
        edges.append((a, b))
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
# Random Haar graphs H(Z_m, S) with |S| = d (fallback for other cases).
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
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
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

    # Phase 1: projective plane incidence graph (D = 3, d-1 prime power).
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # Phase 2: GQ incidence graph (D = 4, d-1 prime power).
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Phase 3: new twin construction on W(d-2) with ILS independent sets, then extension.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            now = time.monotonic()
            twin_deadline = now + 0.6 * max(0.0, deadline - now)
            n2, e2 = _twin2(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    # Phase 4: random Haar graphs if nothing better was found.
    if best[0] <= 2 * d and time.monotonic() < deadline:
        try:
            m_hi = max(d, lib._moore_bound(d, D) // 2)
            m, S = _haar_search(d, D, m_hi, rng, deadline, 1500)
            consider(*lib.haar_graph(m, S))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
