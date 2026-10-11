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
# NEW: bipartite Haar-type lifts over non-abelian groups.
#
# G is a finite group of order m (semidirect Z_mm x| Z_k). Vertices A_x and B_y
# (x, y in G); A_x ~ B_{x s} for s in S, |S| = d. Left multiplication is an
# automorphism, so the graph is vertex-transitive on each side and it suffices
# to check breadth-first reach from A_identity and B_identity. A tabu-free
# simulated annealing searches S to cover everything within distance D.
# ----------------------------------------------------------------------------

def _group_candidates(G, rng, limit=4):
    """Semidirect groups Z_mm x| Z_k of order G = mm*k, as (mm, k, r); r = 1 is abelian. Non-abelian first."""
    nonab, ab = [], []
    for k in range(1, min(G, 12) + 1):
        if G % k:
            continue
        mm = G // k
        if mm < 2:
            continue
        for r in range(1, mm):
            if math.gcd(r, mm) != 1 or pow(r, k, mm) != 1 % mm:
                continue
            (ab if r == 1 else nonab).append((mm, k, r))
    rng.shuffle(nonab)
    rng.shuffle(ab)
    return (nonab + ab)[:limit]


def _group_table(mm, k, r):
    """Multiplication table MT[x, s] = x*s for the semidirect group, element (a, b) coded as a*k + b."""
    G = mm * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, mm) for t in range(k)], dtype=np.int64)
    MT = ((a[:, None] + pw[b][:, None] * a[None, :]) % mm) * k + (b[:, None] + b[None, :]) % k
    return MT.astype(np.int32)


def _cover_cost(MT, INV, S, G, D):
    """Number of (source, vertex) pairs not within distance D, summed over sources A_0 and B_0."""
    IS = INV[S]
    total = 0
    for start in (0, 1):
        visA = np.zeros(G, dtype=bool)
        visB = np.zeros(G, dtype=bool)
        front = np.zeros(1, dtype=np.int64)
        if start == 0:
            visA[0] = True
        else:
            visB[0] = True
        side = start
        for _ in range(D):
            mark = np.zeros(G, dtype=bool)
            if side == 0:
                mark[MT[np.ix_(front, S)].ravel()] = True
                new = mark & ~visB
                visB |= new
            else:
                mark[MT[np.ix_(front, IS)].ravel()] = True
                new = mark & ~visA
                visA |= new
            front = np.flatnonzero(new)
            side ^= 1
            if front.size == 0:
                break
        total += 2 * G - int(visA.sum()) - int(visB.sum())
    return total


def _search_S(MT, INV, G, d, D, deadline, rng):
    """Simulated annealing over connection sets S of size d; return a covering list or None."""
    if d >= G:
        S = list(range(G))
        ok = _cover_cost(MT, INV, np.array(S, dtype=np.int64), G, D) == 0
        return S if ok else None
    Sl = rng.sample(range(G), d)
    cur = _cover_cost(MT, INV, np.array(Sl, dtype=np.int64), G, D)
    while cur > 0:
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        t = rng.randrange(G)
        if t in Sl:
            continue
        old = Sl[i]
        Sl[i] = t
        c = _cover_cost(MT, INV, np.array(Sl, dtype=np.int64), G, D)
        if c <= cur or rng.random() < math.exp(-(c - cur)):
            cur = c
        else:
            Sl[i] = old
    return Sl if cur == 0 else None


def _try_order(G, d, D, deadline, rng):
    """Try to find a covering Haar-type lift on a group of order G; return (n, edges) or None."""
    cands = _group_candidates(G, rng)
    for idx, (mm, k, r) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        sub = now + (deadline - now) / (len(cands) - idx)
        MT = _group_table(mm, k, r)
        INV = np.argmax(MT == 0, axis=1).astype(np.int64)
        S = _search_S(MT, INV, G, d, D, sub, rng)
        if S is not None:
            Sarr = np.array(S, dtype=np.int64)
            xs = np.repeat(np.arange(G, dtype=np.int64), d)
            ys = G + MT[:, Sarr].astype(np.int64).ravel()
            return 2 * G, list(zip(xs.tolist(), ys.tolist()))
    return None


def _haar_phase(d, D, deadline, rng):
    """Binary search on the group order G; return the largest (n, edges) found, or None."""
    lo = d
    hi = min(max(d, lib.moore_bound(d, D) // 2), 1200)
    best = None
    while lo <= hi and time.monotonic() < deadline:
        mid = (lo + hi + 1) // 2
        now = time.monotonic()
        tb = max(0.8, min(6.0, (deadline - now) / 3.0))
        res = _try_order(mid, d, D, min(deadline, now + tb), rng)
        if res is not None:
            best = res
            lo = mid + 1
        else:
            hi = mid - 1
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(0.5, min(0.75 * time_limit, time_limit - 12.0))
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

    # Phase 1: bold change, group-lift Haar graphs over non-abelian groups.
    try:
        res = _haar_phase(d, D, t0 + 0.55 * budget, rng)
        if res is not None:
            consider(*res)
    except Exception:
        pass

    # Phase 2: algebraic constructions (parent pipeline), using the remaining time.
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

    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            now = time.monotonic()
            twin_deadline = now + 0.6 * (deadline - now)
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
