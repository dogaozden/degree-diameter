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

    spare = [v for v in range(n) if len(adj[v]) < d]

    MAX_FAILS = 20000
    fails = 0
    while time.monotonic() < deadline:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline:
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
            spare = [v for v in spare if len(adj[v]) < d]
            if len(S) < d:
                spare.append(x)
            fails = 0
            grown = True
            break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# NEW: bi-Cayley (Haar-type) graphs over finite groups, diameter 4.
#
# Vertices a_x and b_x for x in G (|G| = N). Edge a_x ~ b_{x*s} for s in S,
# |S| = d. Then the graph is bipartite and d-regular on 2N vertices. Diameter
# <= 4 reduces to group covering conditions on S:
#   d1: G = {S} U S S^-1 S                     (a-to-b within 3)
#   d2: G = {e} U T U T T,   T = S S^-1         (a-to-a within 4)
#   d3: G = {e} U T2 U T2 T2, T2 = S^-1 S       (b-to-b within 4)
# A simulated-annealing search drives the total deficit to zero. Groups are
# semidirect products Z_m x| Z_k (r^k = 1 mod m), which include cyclic and
# direct products.
# ----------------------------------------------------------------------------

def _groups(N, rng):
    """Return a shuffled list of (m, k, r) with m*k = N giving semidirect products Z_m x| Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        rs = range(1, m) if m > 1 else [0]
        for r in rs:
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    rng.shuffle(out)
    return out[:12]


def _group_table(m, k, r):
    """Multiplication table M (N x N) and inverse array for Z_m x| Z_k, element (a, b) coded a*k+b."""
    N = m * k
    powers = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    X = np.arange(N, dtype=np.int64)
    a, b = X // k, X % k
    M = ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    pos = np.argwhere(M == 0)
    inv = np.zeros(N, dtype=np.int64)
    inv[pos[:, 0]] = pos[:, 1]
    return M, inv


def _deficit(S, M, inv, N):
    """Total number of group elements not covered by the three diameter conditions."""
    Si = inv[S]
    X = M[S[:, None], Si[None, :]]              # s1 * s2^-1
    Y = M[X[:, :, None], S[None, None, :]]      # s1 * s2^-1 * s3
    mark = np.zeros(N, dtype=bool)
    mark[S] = True
    mark[Y.ravel()] = True
    d1 = N - int(mark.sum())

    T = np.unique(X)
    mark2 = np.zeros(N, dtype=bool)
    mark2[0] = True
    mark2[T] = True
    mark2[M[T[:, None], T[None, :]].ravel()] = True
    d2 = N - int(mark2.sum())

    X2 = M[Si[:, None], S[None, :]]             # s1^-1 * s2
    T2 = np.unique(X2)
    mark3 = np.zeros(N, dtype=bool)
    mark3[0] = True
    mark3[T2] = True
    mark3[M[T2[:, None], T2[None, :]].ravel()] = True
    d3 = N - int(mark3.sum())
    return d1 + d2 + d3


def _anneal(N, d, M, inv, deadline, rng):
    """Search for a d-subset S of G with zero deficit; return it as an array or None."""
    S = np.array(rng.sample(range(N), d), dtype=np.int64)
    f = _deficit(S, M, inv, N)
    best_f, best_S = f, S.copy()
    start = time.monotonic()
    span = max(1e-6, deadline - start)
    temp = 1.0
    it = 0
    while f > 0:
        it += 1
        if (it & 63) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = (now - start) / span
            temp = 1.2 * (1.0 - frac) + 0.05
        i = rng.randrange(d)
        v = rng.randrange(N)
        if np.any(S == v):
            continue
        S2 = S.copy()
        S2[i] = v
        f2 = _deficit(S2, M, inv, N)
        if f2 <= f or rng.random() < math.exp(-(f2 - f) / temp):
            S, f = S2, f2
            if f < best_f:
                best_f, best_S = f, S.copy()
    return best_S if best_f == 0 else None


def _bicayley_route(d, best_n, deadline, rng, consider):
    """Try bi-Cayley graphs of increasing order N above best_n/2; report each valid one via consider."""
    Nmax = lib._moore_bound(d, 4) // 2
    N = best_n // 2 + 1
    while N <= Nmax:
        if time.monotonic() >= deadline - 0.3:
            return
        groups = _groups(N, rng)
        if not groups:
            N += 1
            continue
        found = None
        for idx, (m, k, r) in enumerate(groups):
            now = time.monotonic()
            left = deadline - now
            if left < 0.3:
                break
            slot = left / (len(groups) - idx)
            M, inv = _group_table(m, k, r)
            S = _anneal(N, d, M, inv, now + slot, rng)
            if S is not None:
                found = (M, S)
                break
        if found is None:
            return
        M, S = found
        edges = []
        for s in S.tolist():
            col = M[:, s].tolist()
            edges.extend((x, N + col[x]) for x in range(N))
        consider(2 * N, edges)
        N += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    parent_deadline = t0 + 0.6 * budget
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

    # Twin graph on W(d-2) (degree d), then randomized set-cover extensions.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            twin_deadline = t0 + 0.35 * budget
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            attempts = 3
            for a in range(attempts):
                now = time.monotonic()
                if now >= parent_deadline - 0.5:
                    break
                slice_end = now + (parent_deadline - now) / (attempts - a)
                n3, e3 = _extend(n2, e2, d, min(slice_end, parent_deadline), rng)
                consider(n3, e3)
        except Exception:
            pass

    # NEW route: bi-Cayley graphs over groups, using the remaining time.
    if D == 4 and d >= 3:
        try:
            _bicayley_route(d, best[0], deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
