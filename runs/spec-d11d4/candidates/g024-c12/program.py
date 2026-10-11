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
    c = [0] * n          # number of neighbours of v inside S
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
            # Restart from the best independent set found so far.
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
    padj = [set() for _ in range(P)]          # collinear points
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)
    ladj = [set() for _ in range(L)]          # lines sharing a point
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

NOISE = 0.25


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


def _pick(pool, reach, unc, rng):
    """Choose the next cover vertex from pool: best gain, or a random useful one with prob NOISE."""
    if rng.random() < NOISE:
        useful = [v for v in pool if reach[v] & unc]
        if useful:
            return rng.choice(useful)
        return -1
    best, bv = 0, -1
    for v in pool:
        g = (reach[v] & unc).bit_count()
        if g > best:
            best, bv = g, v
    return bv


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

    MAX_FAILS = 20000
    fails = 0
    while time.monotonic() < deadline:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            if fails >= MAX_FAILS:
                return n, edges
            s0 = rng.choice(spare)
            pool = [v for v in spare if color[v] == color[s0] and v != s0]
            S = [s0]
            unc = full & ~reach[s0]
            while unc and len(S) < d and pool:
                bv = _pick(pool, reach, unc, rng)
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
# NEW: bi-Cayley (Haar-type) graphs over non-abelian groups Z_m x|_r Z_k.
#
# Vertices a_x and b_y for x, y in G. Edge a_x ~ b_{x s} for s in S, |S| = d.
# Left multiplication is an automorphism, so only three BFS-type conditions
# matter (T = S S^-1, U = S^-1 S, group elements as sets):
#   A-A : T.T covers G           (distance <= 4 from a_1 to all a)
#   A-B : S u T.S covers G       (distance <= 3 from a_1 to all b)
#   B-B : U.U covers G           (distance <= 4 from b_1 to all b)
# Order 2|G|. A simulated-annealing search over S minimises the number of
# uncovered elements; a zero gives a valid graph of order 2|G|.
# ----------------------------------------------------------------------------

def _group_candidates(lo, hi, rng):
    """Semidirect groups Z_m x| Z_k with exact action order k, order in [lo, hi], sorted by order."""
    out = []
    for m in range(2, hi + 1):
        k_lo = max(2, -(-lo // m))
        k_hi = hi // m
        for k in range(k_lo, k_hi + 1):
            proper = [j for j in range(1, k) if k % j == 0]
            found = None
            for _ in range(40):
                r = rng.randrange(1, m)
                if math.gcd(r, m) != 1:
                    continue
                if pow(r, k, m) != 1 % m:
                    continue
                if any(pow(r, j, m) == 1 % m for j in proper):
                    continue
                found = r
                break
            if found is not None:
                out.append((m * k, m, k, found))
    out.sort()
    return out


def _semidirect_tables(m, k, r):
    """Return (G, M, INV): multiplication table and inverses for Z_m x| Z_k, element (a,b) coded a*k+b."""
    G = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    X = np.arange(G, dtype=np.int64)
    a = X // k
    b = X % k
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    B = (b[:, None] + b[None, :]) % k
    M = A * k + B
    nb = (-b) % k
    ia = (-(pw[nb] * a)) % m
    INV = ia * k + nb
    return G, M, INV


def _haar_try(d, D, G, M, INV, slice_end, rng, consider):
    """Simulated annealing for a connection set S of size d; return True if a valid graph was accepted."""

    def misses(S):
        Sinv = INV[S]
        T = np.unique(M[S[:, None], Sinv[None, :]])
        cA = np.count_nonzero(np.bincount(M[T[:, None], T[None, :]].ravel(), minlength=G))
        B1 = np.concatenate([S, M[T[:, None], S[None, :]].ravel()])
        cB = np.count_nonzero(np.bincount(B1, minlength=G))
        U = np.unique(M[Sinv[:, None], S[None, :]])
        cU = np.count_nonzero(np.bincount(M[U[:, None], U[None, :]].ravel(), minlength=G))
        return 3 * G - int(cA) - int(cB) - int(cU)

    S = np.array(rng.sample(range(G), d), dtype=np.int64)
    cur = misses(S)
    start = time.monotonic()
    span = max(1e-3, slice_end - start)
    while cur > 0:
        now = time.monotonic()
        if now >= slice_end:
            return False
        temp = 0.6 * (1.0 - (now - start) / span) + 0.02
        i = rng.randrange(d)
        g = rng.randrange(G)
        if g in S:
            continue
        S2 = S.copy()
        S2[i] = g
        new = misses(S2)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, new

    Mx = M[:, S].tolist()
    edges = [(x, G + int(v)) for x in range(G) for v in Mx[x]]
    n = 2 * G
    if lib.is_valid(n, edges, d, D):
        consider(n, edges)
        return True
    return False


def _haar_stage(d, D, lo, hi, deadline, rng, consider):
    """Cycle through a pool of semidirect groups, running short annealing slices on each."""
    cands = _group_candidates(lo, hi, rng)
    if not cands:
        return
    near = [c for c in cands if c[0] <= lo + 40]
    rest = [c for c in cands if c[0] > lo + 40]
    rng.shuffle(near)
    pool = (near + rest)[:12]
    idx = 0
    while True:
        now = time.monotonic()
        if now >= deadline - 0.5:
            return
        _, m, k, r = pool[idx % len(pool)]
        idx += 1
        G, M, INV = _semidirect_tables(m, k, r)
        slice_end = min(deadline, now + 4.0)
        if _haar_try(d, D, G, M, INV, slice_end, rng, consider):
            return


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
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

    # Split the budget: for D = 4 the parent pipeline gets 60%, the new search the rest.
    use_haar = (D == 4 and d >= 3)
    split = 0.6 if use_haar else 1.0
    pdead = t0 + split * budget
    twin_deadline = t0 + 0.5 * split * budget

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

    # Twin graph on W(d-2), then randomized set-cover extension using spare slots.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, pdead, rng)
            consider(n3, e3)
        except Exception:
            pass

    # New search: bi-Cayley graphs over semidirect groups, order must beat current best.
    if use_haar:
        lo = best[0] // 2 + 1
        hi = min(lo + 120, 1500)
        if lo <= hi:
            try:
                _haar_stage(d, D, lo, hi, deadline, rng, consider)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
