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
# Bold alternative: bi-Cayley (group-lift) graphs for diameter 4.
# Base graph: one A vertex and one B vertex, joined by d darts labelled with
# distinct group elements S. Vertices A_x = x, B_y = N + y, edges A_x ~ B_{x*g}.
# Left multiplication is an automorphism, so only the balls around A_e and B_e
# need checking. Connection sets are found by simulated annealing.
# ----------------------------------------------------------------------------

def _group_specs(N, rng):
    """Candidate groups of order N as (m, k, pw): Z_m x| Z_k with element (a,b) coded a*k+b and pw[b] = r^b mod m."""
    specs = [(N, 1, [1])]
    if N % 2 == 0 and N // 2 >= 3:
        m = N // 2
        specs.append((m, 2, [1, m - 1]))  # dihedral-type
    for k in (3, 4, 5, 6):
        if N % k == 0 and N // k >= 3:
            m = N // k
            rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            if rs:
                r = rng.choice(rs)
                specs.append((m, k, [pow(r, b, m) for b in range(k)]))
    return specs


def _tables(m, k, pw):
    """Return (R, Ri) with R[x,g] = x*g and Ri[y,g] = y*g^{-1} for the group Z_m x| Z_k."""
    N = m * k
    X = np.arange(N, dtype=np.int64)
    a = X // k
    b = X % k
    pwa = np.array(pw, dtype=np.int64)
    R = ((a[:, None] + pwa[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    nbv = (-b) % k
    invc = ((-pwa[nbv] * a) % m) * k + nbv
    Ri = R[:, invc]
    return R, Ri


def _cost(S, R, Ri, N):
    """Number of vertices not within distance 4 of A_e plus of B_e (0 means valid)."""
    total = 0
    for start in (0, 1):
        seenA = np.zeros(N, dtype=bool)
        seenB = np.zeros(N, dtype=bool)
        fa = np.zeros(0, dtype=np.int64)
        fb = np.zeros(0, dtype=np.int64)
        if start == 0:
            seenA[0] = True
            fa = np.array([0], dtype=np.int64)
        else:
            seenB[0] = True
            fb = np.array([0], dtype=np.int64)
        for _ in range(4):
            nb = R[np.ix_(fa, S)].ravel() if fa.size else fa
            na = Ri[np.ix_(fb, S)].ravel() if fb.size else fb
            nb = np.unique(nb[~seenB[nb]]) if nb.size else nb
            na = np.unique(na[~seenA[na]]) if na.size else na
            seenB[nb] = True
            seenA[na] = True
            fa, fb = na, nb
            if fa.size == 0 and fb.size == 0:
                break
        total += 2 * N - int(seenA.sum()) - int(seenB.sum())
    return total


def _anneal(d, R, Ri, N, end, rng):
    """Search a d-element connection set with cost 0 before time end; return it or None."""
    S = rng.sample(range(N), d)
    cur = _cost(np.array(S, dtype=np.int64), R, Ri, N)
    while cur > 0 and time.monotonic() < end:
        i = rng.randrange(d)
        g = rng.randrange(N)
        if g in S:
            continue
        S2 = S[:]
        S2[i] = g
        c2 = _cost(np.array(S2, dtype=np.int64), R, Ri, N)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / 0.6):
            S, cur = S2, c2
    return S if cur == 0 else None


def _lift_edges(R, S, N):
    """Edges A_x -- B_{x*g} for x in the group and g in S."""
    xs = np.repeat(np.arange(N, dtype=np.int64), len(S))
    gs = np.tile(np.array(S, dtype=np.int64), N)
    bs = R[xs, gs]
    return [(int(x), int(N + b)) for x, b in zip(xs.tolist(), bs.tolist())]


def _bicayley_stage(d, base_n, deadline, rng):
    """Search bi-Cayley graphs of increasing group order above base_n/2; return the largest valid one found or None."""
    lo = base_n // 2 + 1
    hi = lib._moore_bound(d, 4) // 2
    result = None
    N = lo
    while N <= hi and time.monotonic() < deadline - 0.5:
        for m, k, pw in _group_specs(N, rng):
            now = time.monotonic()
            remaining = deadline - now
            if remaining < 0.5:
                break
            end = now + min(remaining, max(2.0, 0.25 * remaining))
            R, Ri = _tables(m, k, pw)
            S = _anneal(d, R, Ri, N, end, rng)
            if S is not None:
                result = (2 * N, _lift_edges(R, S, N))
                break
        N += 1
    return result


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

    # The parent pipeline gets most of the budget for D = 4; the bi-Cayley search gets the rest.
    parent_deadline = t0 + (0.65 if D == 4 else 1.0) * budget

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
            twin_deadline = min(parent_deadline, t0 + 0.35 * budget)
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

    # Bold alternative for diameter 4: bi-Cayley group lifts, only if they can beat the current best.
    if D == 4 and d >= 3 and time.monotonic() < deadline - 2.0:
        try:
            cand = _bicayley_stage(d, best[0], deadline, rng)
            if cand is not None:
                consider(*cand)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
