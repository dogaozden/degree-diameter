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
# Maximum independent set by iterated local search with (1,2)-swaps.
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    if n == 0:
        return []
    inS = [False] * n
    c = [0] * n
    S = set()
    adjset = [set(a) for a in adj]

    def add(v):
        inS[v] = True
        S.add(v)
        for w in adj[v]:
            c[w] += 1

    def remove(u):
        inS[u] = False
        S.discard(u)
        for w in adj[u]:
            c[w] -= 1

    def local_search():
        while True:
            changed = False
            free = [v for v in range(n) if not inS[v] and c[v] == 0]
            rng.shuffle(free)
            for v in free:
                if not inS[v] and c[v] == 0:
                    add(v)
                    changed = True
            for x in list(S):
                if not inS[x]:
                    continue
                one = [u for u in adj[x] if c[u] == 1]
                if len(one) < 2:
                    continue
                rng.shuffle(one)
                pair = None
                for i in range(len(one)):
                    for j in range(i + 1, len(one)):
                        if one[j] not in adjset[one[i]]:
                            pair = (one[i], one[j])
                            break
                    if pair is not None:
                        break
                if pair is not None:
                    remove(x)
                    add(pair[0])
                    add(pair[1])
                    changed = True
            if not changed:
                break

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if not inS[v] and c[v] == 0:
            add(v)
    local_search()
    best = list(S)
    stale = 0

    while time.monotonic() < deadline:
        cand = [v for v in range(n) if not inS[v]]
        if not cand:
            break
        v = rng.choice(cand)
        for w in adj[v]:
            if inS[w]:
                remove(w)
        add(v)
        local_search()
        if len(S) > len(best):
            best = list(S)
            stale = 0
        else:
            stale += 1
        if len(S) < len(best) - 1 or stale > 300:
            for u in list(S):
                remove(u)
            for u in best:
                add(u)
            stale = 0
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
# Randomized greedy set-cover vertex extension for diameter 4.
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
    """Choose the next cover vertex: best gain, or a random useful one with prob NOISE."""
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
# NEW: bi-Cayley (Haar-type) graphs over small groups, searched by local search.
# Vertices (g,0), (g,1) for g in G; edge (g,0)-(g s,1) for s in S, |S| = d.
# Diameter <= 4 iff, with W = S S^{-1}:
#   (A) S u W S = G,  (B) W W = G,  (C) W' W' = G with W' = S^{-1} S.
# ----------------------------------------------------------------------------

def _moore(d, D):
    return 2 * sum((d - 1) ** i for i in range(D))


def _group_table(kind, N, m, k, P):
    """Multiplication table and inverse array for Z_N (kind 0) or Z_m x|_r Z_k (kind 1, element a*k+b)."""
    x = np.arange(N, dtype=np.int64)
    if kind == 0:
        M = (x[:, None] + x[None, :]) % N
    else:
        A = x // k
        B = x % k
        M = ((A[:, None] + P[B][:, None] * A[None, :]) % m) * k + (B[:, None] + B[None, :]) % k
    inv = np.argmax(M == 0, axis=1)
    return M, inv


def _cost(M, inv, S, N):
    """Number of uncovered elements over conditions (A), (B), (C)."""
    Si = inv[S]
    W2 = np.unique(M[S[:, None], Si[None, :]])
    W3 = np.unique(M[Si[:, None], S[None, :]])
    maskA = np.zeros(N, dtype=bool)
    maskA[S] = True
    maskA[M[W2[:, None], S[None, :]].ravel()] = True
    ca = N - int(maskA.sum())
    maskB = np.zeros(N, dtype=bool)
    maskB[M[W2[:, None], W2[None, :]].ravel()] = True
    cb = N - int(maskB.sum())
    maskC = np.zeros(N, dtype=bool)
    maskC[M[W3[:, None], W3[None, :]].ravel()] = True
    cc = N - int(maskC.sum())
    return ca + cb + cc


def _search(M, inv, N, d, iters, deadline, rng):
    """Simulated-annealing style local search for a connection set S of size d with zero cost."""
    S = np.array(rng.sample(range(N), d), dtype=np.int64)
    cur = _cost(M, inv, S, N)
    for _ in range(iters):
        if cur == 0:
            return S
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        c = rng.randrange(N)
        if (S == c).any():
            continue
        T = S.copy()
        T[i] = c
        cc = _cost(M, inv, T, N)
        if cc <= cur or rng.random() < math.exp(-(cc - cur) / 0.8):
            S, cur = T, cc
    return S if cur == 0 else None


def _candidates(d, lo, width, rng):
    """Groups of order N in [lo, lo+width): cyclic plus a few semidirect products Z_m x| Z_k."""
    cands = []
    for N in range(lo, lo + width):
        cands.append((N, 0, 0, 0, None))
        for k in range(2, min(12, N) + 1):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            rng.shuffle(rs)
            for r in rs[:3]:
                cands.append((N, 1, m, k, r))
    return cands


def _bicayley(d, D, lo, deadline, rng):
    """Search bi-Cayley graphs of degree d; return (n, edges) for the largest group found, else None."""
    cands = _candidates(d, lo, 12, rng)
    best = None  # (N, S, M)
    iters = 800
    while time.monotonic() < deadline:
        for (N, kind, m, k, r) in cands:
            if time.monotonic() >= deadline:
                break
            if best is not None and N <= best[0]:
                continue
            P = None
            if kind == 1:
                P = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
            M, inv = _group_table(kind, N, m, k, P)
            S = _search(M, inv, N, d, iters, deadline, rng)
            if S is not None:
                best = (N, S, M)
        iters *= 2
    if best is None:
        return None
    N, S, M = best
    edges = []
    for s in S.tolist():
        col = M[:, s].tolist()
        for g in range(N):
            edges.append((g, N + col[g]))
    return 2 * N, edges


# ----------------------------------------------------------------------------
# Previous best pipeline (projective plane / GQ / twins + extension), reused as a fallback.
# ----------------------------------------------------------------------------

def _parent(d, D, rng, deadline, best):
    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

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
            span = deadline - now
            n2, e2 = _twin_graph(d - 2, now + 0.35 * span, rng)
            consider(n2, e2)
            attempts = 3
            for a in range(attempts):
                now = time.monotonic()
                if now >= deadline - 0.5:
                    break
                slice_end = now + (deadline - now) / (attempts - a)
                n3, e3 = _extend(n2, e2, d, min(slice_end, deadline), rng)
                consider(n3, e3)
        except Exception:
            pass
    return best


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

    bc_target = None
    if D >= 4 and d >= 3:
        lo = int(0.8 * _moore(d, D)) // 2
        bc_target = 2 * lo
        try:
            res = _bicayley(d, D, lo, t0 + 0.45 * budget, rng)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    # Run the older pipeline only if the bi-Cayley search did not reach its target.
    if bc_target is None or best[0] < bc_target:
        try:
            best = _parent(d, D, rng, deadline, best)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
