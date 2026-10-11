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
# Group helpers.
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


# ----------------------------------------------------------------------------
# NEW CONSTRUCTION: four-orbit bi-Cayley voltage lift (diameter 4).
#
# Vertices: left orbits A0, A1 and right orbits B0, B1, each a copy of a group G
# of order N (total 4N). Each block (u, v) carries a set of distinct voltages
# S_uv in G; left element (u, x) is adjacent to right element (v, x*g) for every
# g in S_uv. Block sizes are S00 = d-k, S01 = k, S10 = k, S11 = d-k, so every
# vertex has degree d. The graph is bipartite (left vs right).
#
# Left translation by h is an automorphism, so the diameter is at most D iff
# every orbit identity (o, e) reaches all 4N vertices within D steps. The check
# is vectorised with numpy on a precomputed neighbour array, and simulated
# annealing repairs unreached vertices by replacing single voltages.
# Random lifts of this shape are already close to diameter 4 at order ~2000,
# so the search is fast and the bisection on N is short.
# ----------------------------------------------------------------------------

def _orbit_nbr(N, d, MT, inv, blocks):
    """Neighbour array (4N x d): left rows 0..2N-1, right rows 2N..4N-1, orbit-major indexing."""
    nbr = np.empty((4 * N, d), dtype=np.int64)
    rows = np.arange(N, dtype=np.int64)
    cL = [0, 0]
    cR = [0, 0]
    for (u, v), G in blocks.items():
        for g in G:
            nbr[u * N:(u + 1) * N, cL[u]] = 2 * N + v * N + MT[rows, g]
            cL[u] += 1
            nbr[2 * N + v * N:2 * N + (v + 1) * N, cR[v]] = u * N + MT[rows, inv[g]]
            cR[v] += 1
    return nbr


def _orbit_cost(N, d, D, MT, inv, blocks):
    """Number of (orbit identity, vertex) pairs at distance > D, summed over the four orbit identities."""
    nbr = _orbit_nbr(N, d, MT, inv, blocks)
    total = 4 * N
    unreached = 0
    for s in (0, N, 2 * N, 3 * N):
        seen = np.zeros(total, dtype=bool)
        seen[s] = True
        frontier = np.array([s], dtype=np.int64)
        for _ in range(D):
            nxt = nbr[frontier].ravel()
            nxt = nxt[~seen[nxt]]
            if nxt.size == 0:
                break
            seen[nxt] = True
            frontier = np.unique(nxt)
        unreached += total - int(seen.sum())
    return unreached


def _orbit_search(N, d, D, MT, inv, k, deadline, rng):
    """Simulated annealing over the four voltage blocks; return (True, blocks) on full coverage else (False, None)."""
    sizes = {(0, 0): d - k, (0, 1): k, (1, 0): k, (1, 1): d - k}
    blocks = {key: rng.sample(range(N), sz) for key, sz in sizes.items()}
    keys = list(blocks)
    cur = _orbit_cost(N, d, D, MT, inv, blocks)
    t_start = time.monotonic()
    span = max(deadline - t_start, 1e-6)
    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t_start) / span
        T = 1.5 * (1.0 - frac) + 0.05
        key = keys[rng.randrange(len(keys))]
        lst = blocks[key]
        i = rng.randrange(len(lst))
        ng = rng.randrange(N)
        while ng in lst:
            ng = rng.randrange(N)
        old = lst[i]
        lst[i] = ng
        c2 = _orbit_cost(N, d, D, MT, inv, blocks)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
        else:
            lst[i] = old
    if cur == 0:
        return True, {key: list(v) for key, v in blocks.items()}
    return False, None


def _orbit_lift(d, D, deadline, rng):
    """Bisection over group order N for the largest four-orbit lift of diameter <= D; return (N, m, k, r, kc, blocks) or None."""
    if D != 4 or d < 3:
        return None
    moore = lib._moore_bound(d, D)
    lo = max(d + 1, moore // 6)
    hi = moore // 4          # 4N vertices must not exceed the Moore bound
    best = None
    while lo <= hi and time.monotonic() < deadline:
        N = (lo + hi + 1) // 2
        now = time.monotonic()
        slot_end = min(deadline, now + max(2.0, (deadline - now) / 3.0))
        found = None
        while time.monotonic() < slot_end and found is None:
            m, k, r = rng.choice(_group_options(N))
            MT = _mul_table(m, k, r)
            inv = np.argmax(MT == 0, axis=1).astype(np.int64)
            kc = rng.randint(1, d - 1)
            sub_end = min(slot_end, time.monotonic() + 3.0)
            ok, blocks = _orbit_search(N, d, D, MT, inv, kc, sub_end, rng)
            if ok:
                found = (N, m, k, r, kc, blocks)
        if found is not None:
            best = found
            lo = found[0] + 1
        else:
            hi = N - 1
    return best


def _orbit_graph(d, N, m, k, r, blocks):
    """Materialise a four-orbit lift as (4N, edges)."""
    MT = _mul_table(m, k, r)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    nbr = _orbit_nbr(N, d, MT, inv, blocks)
    us = np.repeat(np.arange(2 * N, dtype=np.int64), d)
    vs = nbr[:2 * N].ravel()
    return 4 * N, list(zip(us.tolist(), vs.tolist()))


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 12.0))
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

    # New construction: four-orbit bi-Cayley voltage lift, searched by vectorised SA.
    if D >= 4:
        try:
            res = _orbit_lift(d, D, t0 + 0.7 * budget, rng)
            if res is not None:
                N, m, k, r, kc, blocks = res
                consider(*_orbit_graph(d, N, m, k, r, blocks))
        except Exception:
            pass

    # Twin construction on W(d-2) using the spare degree slot (degree d, diameter 4).
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            consider(*_twin_graph(d - 2, deadline, rng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
