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


def _cover_attempt(s0, pool_all, reach, full, d, rng, noise):
    """Cover all vertices using R3(s0) plus up to d-1 pool vertices; return the chosen set S or None."""
    S = [s0]
    unc = full & ~reach[s0]
    pool = [v for v in pool_all if v != s0]
    while unc and len(S) < d and pool:
        gains = [(reach[v] & unc).bit_count() for v in pool]
        best = max(gains)
        if best <= 0:
            break
        if noise > 0.0 and rng.random() < noise:
            thresh = max(1, int(best * 0.8))
            choices = [i for i, g in enumerate(gains) if g >= thresh]
            i = rng.choice(choices)
        else:
            top = [i for i, g in enumerate(gains) if g == best]
            i = rng.choice(top)
        bv = pool[i]
        S.append(bv)
        unc &= ~reach[bv]
        pool[i] = pool[-1]
        pool.pop()
    if unc:
        return None
    return S


def _extend(n, edges, d, deadline, rng, max_fails):
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
    while time.monotonic() < deadline and fails < max_fails:
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        s0 = rng.choice(spare)
        pool_all = [v for v in spare if color[v] == color[s0]]
        S = None
        for attempt in range(4):
            noise = 0.0 if attempt == 0 else rng.choice([0.2, 0.35, 0.5])
            S = _cover_attempt(s0, pool_all, reach, full, d, rng, noise)
            if S is not None:
                break
        if S is None:
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
    return n, edges


# ----------------------------------------------------------------------------
# NEW: bipartite Z_m voltage-lift search (different construction).
#
# Base: k A-vertices and k B-vertices joined by d perfect matchings (degree d),
# each dart carrying a voltage in Z_m. The lift has 2*k*m vertices.
# The lift is invariant under translation of the fibres, so diameter <= D
# holds iff, for each of the 2k base vertices, the radius-D ball of its
# fibre-0 copy covers every lifted vertex. Coverage is computed with
# boolean arrays over Z_m (np.roll = shift by a voltage), all base reps at once.
# Simulated annealing on voltages and matching targets minimises uncovered pairs.
# ----------------------------------------------------------------------------

def _lift_eval(k, m, D, P, Vol):
    """Return (uncovered count, darts) for the lift; darts are (A index, B index in 2k labels, voltage)."""
    R = 2 * k
    darts = [(a, k + P[r][a], Vol[a][r]) for a in range(k) for r in range(len(P))]
    F = np.zeros((R, R, m), dtype=bool)
    idx = np.arange(R)
    F[idx, idx, 0] = True
    V = F.copy()
    for _ in range(D):
        New = np.zeros_like(F)
        for a, b, v in darts:
            New[:, b, :] |= np.roll(F[:, a, :], v, axis=-1)
            New[:, a, :] |= np.roll(F[:, b, :], -v, axis=-1)
        F = New & ~V
        V |= F
    return int((~V).sum()), darts


def _lift_attempt(k, m, d, D, deadline, rng):
    """Search voltages for a Z_m lift of the k,k base with degree d and diameter D; return darts or None."""

    def fresh():
        P = []
        for _ in range(d):
            perm = list(range(k))
            rng.shuffle(perm)
            P.append(perm)
        Vol = [[rng.randrange(m) for _ in range(d)] for _ in range(k)]
        return P, Vol

    P, Vol = fresh()
    cost, _ = _lift_eval(k, m, D, P, Vol)
    best_seen = cost
    stale = 0
    T = 0.6
    while cost > 0:
        if time.monotonic() > deadline:
            return None
        stale += 1
        if stale > 2500:
            P, Vol = fresh()
            cost, _ = _lift_eval(k, m, D, P, Vol)
            best_seen = cost
            stale = 0
            continue
        if k == 1 or rng.random() < 0.6:
            a = rng.randrange(k)
            r = rng.randrange(d)
            old = Vol[a][r]
            new = rng.randrange(m)
            if new == old:
                continue
            Vol[a][r] = new
            c2, _ = _lift_eval(k, m, D, P, Vol)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                Vol[a][r] = old
        else:
            r = rng.randrange(d)
            a1, a2 = rng.sample(range(k), 2)
            row = P[r]
            row[a1], row[a2] = row[a2], row[a1]
            c2, _ = _lift_eval(k, m, D, P, Vol)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                row[a1], row[a2] = row[a2], row[a1]
        if cost < best_seen:
            best_seen = cost
            stale = 0
    _, darts = _lift_eval(k, m, D, P, Vol)
    return darts


def _lift_phase(d, D, moore, best_n, deadline, rng):
    """Increase the lift order over several base sizes k; return the best valid (n, edges) found or None."""
    best = None
    cur = best_n
    for k in (2, 3, 4, 1, 5, 6):
        if time.monotonic() >= deadline:
            break
        m_max = moore // (2 * k)
        m = max(2, -(-(cur + 2) // (2 * k)))
        if m > m_max:
            continue
        found_here = False
        while m <= m_max and time.monotonic() < deadline:
            now = time.monotonic()
            left = deadline - now
            slice_end = min(deadline, now + max(1.0, min(8.0, 0.3 * left)))
            darts = _lift_attempt(k, m, d, D, slice_end, rng)
            if darts is None:
                if found_here:
                    break
                m -= max(1, m // 60)
                if m < 2:
                    break
                continue
            triples = [(a, b, v) for a, b, v in darts]
            n, edges = lib.voltage_lift(2 * k, triples, m)
            if n > cur and lib.is_valid(n, edges, d, D):
                cur = n
                best = (n, edges)
                found_here = True
            else:
                break
            m += max(1, m // 80)
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    pdeadline = t0 + 0.5 * budget
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
            return True
        return False

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

    # Twin graph on W(d-2) plus randomized set-cover extensions.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        base = None
        try:
            now = time.monotonic()
            base = _twin_graph(d - 2, now + 0.35 * (pdeadline - now), rng)
            consider(*base)
        except Exception:
            base = None

        if base is not None and lib.is_valid(base[0], base[1], d, D):
            ext_best = base
            stagnant = 0
            while time.monotonic() < pdeadline - 0.5 and stagnant < 6:
                now = time.monotonic()
                remaining = pdeadline - now
                run_end = min(pdeadline, now + max(2.0, remaining / 3.0))
                if rng.random() < 0.5:
                    start = ext_best
                else:
                    start = base
                try:
                    n3, e3 = _extend(start[0], start[1], d, run_end, rng, 3000)
                except Exception:
                    stagnant += 1
                    continue
                if n3 > ext_best[0] and lib.is_valid(n3, e3, d, D):
                    ext_best = (n3, e3)
                    consider(n3, e3)
                    stagnant = 0
                else:
                    stagnant += 1

    # New construction: bipartite Z_m voltage-lift search for the remaining time.
    moore = lib.moore_bound(d, D)
    if D >= 2 and d >= 2 and best[0] < moore and time.monotonic() < deadline:
        try:
            res = _lift_phase(d, D, moore, best[0], deadline, rng)
        except Exception:
            res = None
        if res is not None:
            consider(*res)

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
