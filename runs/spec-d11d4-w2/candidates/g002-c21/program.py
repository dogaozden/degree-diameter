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
# Maximum independent set by iterated local search (ARW-style (1,2)-swaps).
# ----------------------------------------------------------------------------

def _mis_ils(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    adjs = [set(a) for a in adj]
    inS = [False] * n
    tight = [0] * n
    sol = []
    pos = [-1] * n

    def add(v):
        inS[v] = True
        pos[v] = len(sol)
        sol.append(v)
        for w in adj[v]:
            tight[w] += 1

    def rem(v):
        inS[v] = False
        i = pos[v]
        last = sol[-1]
        sol[i] = last
        pos[last] = i
        sol.pop()
        pos[v] = -1
        for w in adj[v]:
            tight[w] -= 1

    def fill():
        free = [v for v in range(n) if not inS[v] and tight[v] == 0]
        rng.shuffle(free)
        for v in free:
            if not inS[v] and tight[v] == 0:
                add(v)

    def two_improve():
        while time.monotonic() < deadline:
            moved = False
            order = list(sol)
            rng.shuffle(order)
            for x in order:
                cand = [w for w in adj[x] if tight[w] == 1]
                if len(cand) < 2:
                    continue
                rng.shuffle(cand)
                pair = None
                for i in range(len(cand)):
                    a = cand[i]
                    for j in range(i + 1, len(cand)):
                        b = cand[j]
                        if b not in adjs[a]:
                            pair = (a, b)
                            break
                    if pair is not None:
                        break
                if pair is not None:
                    rem(x)
                    add(pair[0])
                    add(pair[1])
                    fill()
                    moved = True
                    break
            if not moved:
                return

    fill()
    two_improve()
    best = list(sol)
    noimp = 0
    while time.monotonic() < deadline:
        v = rng.randrange(n)
        if inS[v]:
            continue
        for w in adj[v]:
            if inS[w]:
                rem(w)
        add(v)
        fill()
        two_improve()
        if len(sol) > len(best):
            best = list(sol)
            noimp = 0
        else:
            noimp += 1
            if noimp > 400:
                for u in list(sol):
                    rem(u)
                for u in best:
                    add(u)
                noimp = 0
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
# ----------------------------------------------------------------------------

def _twin_parts(q, deadline, rng):
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
    span = max(deadline - now, 0.5)
    I = _mis_ils(P, [sorted(s) for s in padj], now + 0.35 * span, rng)
    J = _mis_ils(L, [sorted(s) for s in ladj], now + 0.70 * span, rng)
    return P, lines, pl, I, J


def _twin_edges(P, lines, pl, I, J):
    L = len(lines)
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
# Extension: add extra degree-d vertices into the spare slots of the twin graph.
# A new line-side vertex Z is joined to d points that dominate all points of W(q)
# in collinearity; a new point-side vertex X is joined to d lines dominating all
# lines. Dominance gives diameter 4 to the new vertex; the cross-parity pairs
# (X, Z) need a shared line/point, enforced as a penalty. Result is always
# verified with lib.is_valid before use.
# ----------------------------------------------------------------------------

def _grow(pool, k, cover_of, aux_of, existing, full, deadline, rng):
    """SA: pick k pool items whose cover_of masks OR to `full`, and whose aux_of union meets every mask in existing."""
    if len(pool) < k:
        return None

    def score(S):
        cov = 0
        aux = 0
        for c in S:
            cov |= cover_of[c]
            aux |= aux_of[c]
        bad = 0
        for e in existing:
            if not (e & aux):
                bad += 1
        return (full & ~cov).bit_count() + 40 * bad

    S = rng.sample(pool, k)
    cur = score(S)
    t0 = time.monotonic()
    span = max(deadline - t0, 1e-6)
    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        T = 1.5 * (1.0 - frac) + 0.05
        i = rng.randrange(k)
        new = pool[rng.randrange(len(pool))]
        if new in S:
            continue
        S2 = list(S)
        S2[i] = new
        c2 = score(S2)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            S, cur = S2, c2
    return S if cur == 0 else None


def _extend(P, lines, pl, I, J, n, edges, d, deadline, rng):
    L = len(lines)
    k = d
    onJ = [False] * P
    for j in J:
        for p in lines[j]:
            onJ[p] = True
    lineFull = [False] * L
    for p in I:
        for j in pl[p]:
            lineFull[j] = True
    pool_p = {p for p in range(P) if not onJ[p]}
    pool_l = {j for j in range(L) if not lineFull[j]}

    # Closed collinearity neighbourhoods of points and lines, as bitmasks.
    NP = []
    for p in range(P):
        m = 0
        for j in pl[p]:
            for r in lines[j]:
                m |= 1 << r
        NP.append(m)
    NL = []
    for j in range(L):
        m = 0
        for p in lines[j]:
            for jj in pl[p]:
                m |= 1 << jj
        NL.append(m)
    PT = []
    for j in range(L):
        m = 0
        for p in lines[j]:
            m |= 1 << p
        PT.append(m)
    PB = [1 << p for p in range(P)]
    fullP = (1 << P) - 1
    fullL = (1 << L) - 1

    edges = list(edges)
    Zmasks = []
    Xpu = []
    while time.monotonic() < deadline:
        progressed = False
        if len(pool_p) >= k:
            sub = min(deadline, time.monotonic() + 3.0)
            S = _grow(sorted(pool_p), k, NP, PB, Xpu, fullP, sub, rng)
            if S is not None:
                zm = 0
                for p in S:
                    zm |= 1 << p
                zid = n
                n += 1
                for p in S:
                    edges.append((p, zid))
                Zmasks.append(zm)
                pool_p -= set(S)
                progressed = True
        if len(pool_l) >= k:
            sub = min(deadline, time.monotonic() + 3.0)
            S = _grow(sorted(pool_l), k, NL, PT, Zmasks, fullL, sub, rng)
            if S is not None:
                pu = 0
                for j in S:
                    pu |= PT[j]
                xid = n
                n += 1
                for j in S:
                    edges.append((xid, P + j))
                Xpu.append(pu)
                pool_l -= set(S)
                progressed = True
        if not progressed:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Bi-Cayley fallback (kept for cases without a twin construction).
# ----------------------------------------------------------------------------

def _group_options(N):
    """Return (m, k, r) choices giving groups of order N: cyclic Z_N and Z_m x|_r Z_k."""
    opts = [(N, 1, 1)]
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _mul_table(m, k, r):
    """Full multiplication table of Z_m x|_r Z_k with element (a, b) coded as a*k+b (identity is 0)."""
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(m * k, dtype=np.int64)
    a = (x // k)[:, None]
    b = (x % k)[:, None]
    c = (x // k)[None, :]
    dd = (x % k)[None, :]
    na = (a + pw[b] * c) % m
    nb = (b + dd) % k
    return na * k + nb


def _sa_search(N, MT, inv, d, M3, deadline, rng):
    """Simulated annealing over connection sets S; return (True, S) on full coverage, else (False, best S)."""

    def cost(S):
        Q = MT[S[:, None], inv[S][None, :]]
        W = MT[Q[:, :, None], S[None, None, :]]
        cov = np.zeros(N, dtype=bool)
        cov[W[M3]] = True
        cov[S] = True
        return N - int(cov.sum())

    S = np.array(rng.sample(range(N), d), dtype=np.int64)
    cur = cost(S)
    best = cur
    bestS = S.copy()
    t_start = time.monotonic()
    span = max(deadline - t_start, 1e-6)
    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t_start) / span
        T = 1.5 * (1.0 - frac) + 0.1
        p = rng.randrange(d)
        inS = set(S.tolist())
        new = rng.randrange(N)
        while new in inS:
            new = rng.randrange(N)
        S2 = S.copy()
        S2[p] = new
        c2 = cost(S2)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            S = S2
            cur = c2
            if cur < best:
                best = cur
                bestS = S.copy()
    return cur == 0, bestS


def _find_connection_set(N, d, deadline, rng):
    """Try random groups of order N with SA on S until deadline; return (m, k, r, S) or None."""
    if N < d + 1:
        return None
    opts = _group_options(N)
    M3 = (~np.eye(d, dtype=bool))[:, :, None] & (~np.eye(d, dtype=bool))[None, :, :]
    while time.monotonic() < deadline:
        m, k, r = rng.choice(opts)
        MT = _mul_table(m, k, r)
        inv = np.argmax(MT == 0, axis=1).astype(np.int64)
        sub_deadline = min(deadline, time.monotonic() + 0.7)
        ok, S = _sa_search(N, MT, inv, d, M3, sub_deadline, rng)
        if ok:
            return (m, k, r, [int(s) for s in S])
    return None


def _bicayley(d, D, deadline, rng):
    """Bisection over group order N for the largest bi-Cayley graph of diameter <= D; return (n, edges) or None."""
    if D != 4 or d < 3:
        return None
    moore = lib._moore_bound(d, D)
    lo, hi = max(d + 1, 2), moore // 2
    best = None
    while lo <= hi and time.monotonic() < deadline:
        N = (lo + hi + 1) // 2
        slot_end = min(deadline, time.monotonic() + 2.5)
        res = _find_connection_set(N, d, slot_end, rng)
        if res is not None:
            best = (N, res)
            lo = N + 1
        else:
            hi = N - 1
    if best is None:
        return None
    N, (m, k, r, S) = best
    order, mul = lib.semidirect_group(m, k, r)
    darts = [(0, 1, g) for g in S]
    return lib.group_lift(2, darts, order, mul)


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

    # Twin construction on W(d-2) with ILS independent sets, then slot extension.
    twin_ok = D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11
    if twin_ok:
        try:
            P, lines, pl, I, J = _twin_parts(d - 2, deadline, rng)
            n, edges = _twin_edges(P, lines, pl, I, J)
            consider(n, edges)
            n2, e2 = _extend(P, lines, pl, I, J, n, edges, d, deadline, rng)
            if n2 > n:
                consider(n2, e2)
        except Exception:
            pass

    # Bi-Cayley fallback only when no twin construction applies.
    if D >= 4 and not twin_ok:
        try:
            res = _bicayley(d, D, t0 + 0.6 * budget, rng)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
