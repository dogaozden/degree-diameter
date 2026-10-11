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

def _ils_mis(n, adj, deadline, rng, target):
    """Return a large independent set (ILS with (1,2)-swaps and perturbation) found before deadline.

    Stops early once the set reaches `target` (a proven upper bound).
    """
    adjset = [set(a) for a in adj]
    inS = [False] * n
    t = [0] * n          # t[v] = number of neighbours of v inside the solution
    S = set()

    def add(v):
        inS[v] = True
        S.add(v)
        for w in adj[v]:
            t[w] += 1

    def rem(v):
        inS[v] = False
        S.discard(v)
        for w in adj[v]:
            t[w] -= 1

    def improve():
        changed = True
        while changed:
            changed = False
            for v in range(n):
                if not inS[v] and t[v] == 0:
                    add(v)
                    changed = True
            for x in list(S):
                if not inS[x]:
                    continue
                # 1-tight neighbours of x: their only solution neighbour is x.
                L = [v for v in adj[x] if t[v] == 1]
                if len(L) < 2:
                    continue
                pair = None
                for i in range(len(L)):
                    sa = adjset[L[i]]
                    for j in range(i + 1, len(L)):
                        if L[j] not in sa:
                            pair = (L[i], L[j])
                            break
                    if pair:
                        break
                if pair:
                    rem(x)
                    add(pair[0])
                    add(pair[1])
                    changed = True

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if not inS[v] and t[v] == 0:
            add(v)
    improve()
    best = list(S)

    while len(best) < target and time.monotonic() < deadline:
        cands = [v for v in range(n) if not inS[v] and t[v] <= 2]
        v = rng.choice(cands) if cands else rng.randrange(n)
        if inS[v]:
            continue
        for w in list(adj[v]):
            if inS[w]:
                rem(w)
        add(v)
        improve()
        if len(S) > len(best):
            best = list(S)
        elif len(S) < len(best) - 2:
            # Restore the best solution to escape a drifting region.
            for u in list(S):
                rem(u)
            for u in best:
                add(u)
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
#
# Points I form an independent set in the collinearity graph (each line gets
# at most one new point-neighbour), lines J form an independent set in the
# concurrency graph (each point gets at most one new line-neighbour). Both are
# bounded by q^2+1 (a spread / ovoid size), so that is the search target.
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

    target = q * q + 1
    now = time.monotonic()
    mid = now + (deadline - now) / 2.0
    I = _ils_mis(P, [sorted(s) for s in padj], mid, rng, target)
    # Unused time from I flows to J because J's deadline is the full deadline.
    J = _ils_mis(L, [sorted(s) for s in ladj], deadline, rng, target)

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
# Bi-Cayley (Haar-type) graphs over small groups with optimized connection sets.
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

    # Twin construction on W(d-2) using the spare degree slot (degree d, diameter 4).
    # It gets the main share of the budget; bi-Cayley search is only a fallback.
    twin_done = False
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            consider(*_twin_graph(d - 2, deadline, rng))
            twin_done = True
        except Exception:
            pass

    if D >= 4 and not twin_done:
        try:
            res = _bicayley(d, D, t0 + 0.6 * budget, rng)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
