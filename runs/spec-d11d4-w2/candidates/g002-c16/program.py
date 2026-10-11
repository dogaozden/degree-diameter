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
# NEW BOLD CONSTRUCTION: multi-block voltage lifts with simulated annealing.
#
# Base: p A-vertices and p B-vertices. Darts (i, j) carry voltages g in a
# finite group G of order N. A-vertex (i, x) is joined to B-vertex (j, x*g) for
# every dart (i, j, g). The total degree is d on each side. Left translation
# by any h in G is an automorphism, so the diameter is at most 4 iff every
# block representative (i, e) reaches all 2pN vertices within 4 steps.
# Voltages are annealed to minimise the number of uncovered (source, target)
# pairs. Bisection over N finds the largest feasible lift; every candidate is
# verified with lib.is_valid before it is used.
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


def _layout(darts, p):
    """Slot index of each dart in its A-row and in its B-column."""
    E = len(darts)
    sa = [0] * E
    sb = [0] * E
    cntA = [0] * p
    cntB = [0] * p
    for t, (i, j) in enumerate(darts):
        sa[t] = cntA[i]
        cntA[i] += 1
        sb[t] = cntB[j]
        cntB[j] += 1
    return sa, sb


def _set_dart(nb, MT, INV, darts, sa, sb, volt, t, N, p, xs):
    """Write the two neighbour slots contributed by dart t."""
    i, j = darts[t]
    g = volt[t]
    pN = p * N
    nb[i * N + xs, sa[t]] = pN + j * N + MT[xs, g]
    nb[pN + j * N + xs, sb[t]] = i * N + MT[xs, INV[g]]


def _cover_cost(nb, sources, n):
    """Total number of vertices not reached within 4 steps, summed over the given source vertices."""
    total = 0
    for s in sources:
        vis = np.zeros(n, dtype=bool)
        vis[s] = True
        front = np.array([s], dtype=np.int64)
        for _ in range(4):
            tgt = nb[front].ravel()
            new = np.zeros(n, dtype=bool)
            new[tgt] = True
            new &= ~vis
            if not new.any():
                break
            vis |= new
            front = np.flatnonzero(new)
        total += n - int(vis.sum())
    return total


def _lift_anneal(N, p, d, MT, INV, darts, sub_deadline, rng):
    """Anneal voltages until the lift has diameter <= 4; return the voltage list or None."""
    E = len(darts)
    n = 2 * p * N
    pN = p * N
    xs = np.arange(N, dtype=np.int64)
    sa, sb = _layout(darts, p)
    groups = {}
    for t, key in enumerate(darts):
        groups.setdefault(key, []).append(t)

    volt = [0] * E
    for ts in groups.values():
        for t, v in zip(ts, rng.sample(range(N), len(ts))):
            volt[t] = v

    nb = np.zeros((n, d), dtype=np.int64)
    for t in range(E):
        _set_dart(nb, MT, INV, darts, sa, sb, volt, t, N, p, xs)
    sources = [i * N for i in range(p)] + [pN + j * N for j in range(p)]

    cur = _cover_cost(nb, sources, n)
    best = cur
    bestv = list(volt)
    start = time.monotonic()
    span = max(sub_deadline - start, 1e-6)
    while cur > 0:
        now = time.monotonic()
        if now >= sub_deadline:
            break
        frac = (now - start) / span
        T = max(0.03, 2.0 * (1.0 - frac))
        t = rng.randrange(E)
        ts = groups[darts[t]]
        used = {volt[u] for u in ts}
        new = rng.randrange(N)
        while new in used:
            new = rng.randrange(N)
        old = volt[t]
        volt[t] = new
        _set_dart(nb, MT, INV, darts, sa, sb, volt, t, N, p, xs)
        c2 = _cover_cost(nb, sources, n)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
            if cur < best:
                best = cur
                bestv = list(volt)
        else:
            volt[t] = old
            _set_dart(nb, MT, INV, darts, sa, sb, volt, t, N, p, xs)
    return bestv if best == 0 else None


def _try_lift(N, p, d, deadline, rng):
    """Random groups and block patterns of order N until an annealing run succeeds; return lift data or None."""
    if N < d + 1:
        return None
    opts = _group_options(N)
    while time.monotonic() < deadline:
        m, k, r = rng.choice(opts)
        MT = _mul_table(m, k, r)
        INV = np.argmax(MT == 0, axis=1).astype(np.int64)
        if p == 1:
            darts = [(0, 0)] * d
        else:
            a = rng.randint(1, d - 1)
            darts = [(0, 0)] * a + [(0, 1)] * (d - a) + [(1, 0)] * (d - a) + [(1, 1)] * a
        sub = min(deadline, time.monotonic() + 0.8)
        volts = _lift_anneal(N, p, d, MT, INV, darts, sub, rng)
        if volts is not None:
            return (MT, INV, darts, volts)
    return None


def _lift_graph(N, p, d, MT, INV, darts, volts):
    """Materialise the lift as (n, edges)."""
    pN = p * N
    xs = np.arange(N, dtype=np.int64)
    nb = np.zeros((2 * pN, d), dtype=np.int64)
    sa, sb = _layout(darts, p)
    for t in range(len(darts)):
        _set_dart(nb, MT, INV, darts, sa, sb, volts, t, N, p, xs)
    edges = []
    for u in range(pN):
        for v in nb[u].tolist():
            edges.append((u, v))
    return 2 * pN, edges


def _search_lift(p, d, D, best_n, deadline, rng):
    """Bisection over N for the largest feasible p-block lift that beats best_n; return (N, data) or None."""
    moore = lib._moore_bound(d, D)
    lo = max(d + 1, best_n // (2 * p) + 1)
    hi = moore // (2 * p)
    found = None
    while lo <= hi and time.monotonic() < deadline:
        mid = (lo + hi) // 2
        slot_end = min(deadline, time.monotonic() + 2.0)
        res = _try_lift(mid, p, d, slot_end, rng)
        if res is not None:
            found = (mid, res)
            lo = mid + 1
        else:
            hi = mid - 1
    return found


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    total_end = t0 + max(2.0, min(50.0, time_limit - 10.0))
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

    # Twin construction on W(d-2) (degree d, diameter 4): proven baseline, gets a fixed share of time.
    twin_ok = D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11
    if twin_ok:
        try:
            twin_end = t0 + 0.6 * (total_end - t0)
            consider(*_twin_graph(d - 2, twin_end, rng))
        except Exception:
            pass

    # Bold path: multi-block voltage lifts searched by annealing, for diameter 4.
    if D >= 4 and d >= 3:
        try:
            rem = total_end - time.monotonic()
            p2_end = time.monotonic() + 0.5 * rem
            for p, phase_end in ((2, p2_end), (1, total_end)):
                if time.monotonic() >= phase_end:
                    continue
                found = _search_lift(p, d, D, best[0], phase_end, rng)
                if found is not None:
                    N, (MT, INV, darts, volts) = found
                    n, edges = _lift_graph(N, p, d, MT, INV, darts, volts)
                    consider(n, edges)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
