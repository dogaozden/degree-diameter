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
# Non-abelian voltage lifts over semidirect products Z_m x| Z_kk.
#
# Base graph: k vertices on side A (0..k-1) and k on side B (k..2k-1). It has d
# darts; dart i joins A-vertex u to B-vertex k+perm_i[u], carrying a voltage
# g in G. The lift has vertex (b, x), x in G, id = b*N + x, and edges
# (u, x)-(v, x*g). The lift is bipartite and each vertex has degree <= d. Left
# multiplication by G is an automorphism, so the diameter is <= D iff every
# base vertex's identity copy reaches all 2kN vertices within D steps.
#
# The score is the number of unreached (source, target) pairs. All 2k sources
# are propagated together with numpy boolean arrays, so one evaluation costs
# a few milliseconds. Group elements are coded (a, b) -> a*kk + b with product
# (a, b)(c, d) = (a + r^b c, b + d) mod (m, kk). This generalises the cyclic
# lifts, which are the case kk = 1.
# ----------------------------------------------------------------------------

def _group_table(m, kk, r):
    """Return (N, M, inv): multiplication table (numpy) and inverse indices of Z_m x|_r Z_kk."""
    N = m * kk
    x = np.arange(N, dtype=np.int64)
    a = x // kk
    b = x % kk
    pw = np.array([pow(r, t, m) for t in range(kk)], dtype=np.int64)
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    B = (b[:, None] + b[None, :]) % kk
    M = A * kk + B
    inv = np.argmax(M == 0, axis=1).astype(np.int64)
    return N, M, inv


def _pick_group(m, kk, rng):
    """Random valid r for Z_m x|_r Z_kk (r^kk = 1 mod m, gcd(r, m) = 1). r = 1 gives the direct product."""
    if m == 1:
        return 0
    valid = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m]
    return rng.choice(valid) if valid else 1


def _lift_edges(d, k, N, M, perm, volt):
    """Return (n, edges) for the lift described by perm and voltages."""
    E = set()
    for i in range(d):
        for u in range(k):
            v = k + perm[i][u]
            g = volt[i][u]
            col = M[:, g].tolist()  # x -> x*g
            for x in range(N):
                a = u * N + x
                b = v * N + col[x]
                E.add((a, b) if a < b else (b, a))
    return 2 * k * N, sorted(E)


def _lift_search(d, D, k, N, M, inv, rng, deadline):
    """Hill-climb voltages and matchings for a zero-defect lift; return (n, edges) or None."""
    nb = 2 * k
    FWD = M[:, inv]  # FWD[y, g] = y * g^{-1}

    def score(perm, volt):
        us, vs, gs = [], [], []
        for i in range(d):
            pi = perm[i]
            vi = volt[i]
            for u in range(k):
                us.append(u)
                vs.append(k + pi[u])
                gs.append(vi[u])
        U = np.array(us, dtype=np.int64)
        V = np.array(vs, dtype=np.int64)
        G = np.array(gs, dtype=np.int64)
        PF = FWD[:, G].T  # forward dart U->V
        PB = M[:, G].T    # reverse dart V->U
        src = np.concatenate([U, V])
        dst = np.concatenate([V, U])
        PERM = np.concatenate([PF, PB])
        E = len(src)
        R = np.zeros((nb, nb, N), dtype=bool)
        for b0 in range(nb):
            R[b0, b0, 0] = True
        for _ in range(D):
            vals = R[:, src[:, None], PERM]
            new = R.copy()
            for e in range(E):
                new[:, dst[e], :] |= vals[:, e, :]
            R = new
        return nb * nb * N - int(R.sum())

    def fresh():
        perm = [rng.sample(range(k), k) for _ in range(d)]
        volt = [[rng.randrange(N) for _ in range(k)] for _ in range(d)]
        return perm, volt

    perm, volt = fresh()
    cur = score(perm, volt)
    stall = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        stall += 1
        if stall > 300:
            perm, volt = fresh()
            cur = score(perm, volt)
            stall = 0
            continue
        if k >= 2 and rng.random() < 0.3:
            i = rng.randrange(d)
            u, u2 = rng.sample(range(k), 2)
            p = perm[i]
            p[u], p[u2] = p[u2], p[u]
            new = score(perm, volt)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                p[u], p[u2] = p[u2], p[u]
        else:
            i = rng.randrange(d)
            u = rng.randrange(k)
            old = volt[i][u]
            volt[i][u] = rng.randrange(N)
            new = score(perm, volt)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                volt[i][u] = old
    return _lift_edges(d, k, N, M, perm, volt)


def _lift_phase(d, D, best_n, deadline, rng, consider):
    """Search group lifts of growing order above the current best until the deadline or the Moore bound."""
    moore = lib._moore_bound(d, D)
    best = best_n
    while time.monotonic() < deadline - 0.5 and best < moore:
        ks = [k for k in range(1, 7) if 2 * k * (best // (2 * k) + 1) <= moore]
        if not ks:
            break
        k = rng.choice(ks)
        lo = best // (2 * k) + 1
        hi = moore // (2 * k)
        # Skew towards small orders, so the search climbs one step at a time.
        N = lo + int((hi - lo) * rng.random() ** 2)
        divs = [kk for kk in range(1, min(8, N) + 1) if N % kk == 0]
        kk = rng.choice(divs)
        m = N // kk
        r = _pick_group(m, kk, rng)
        _, M, inv = _group_table(m, kk, r)
        now = time.monotonic()
        slice_end = min(deadline, now + max(2.5, min(8.0, (deadline - now) / 4.0)))
        res = _lift_search(d, D, k, N, M, inv, rng, slice_end)
        if res is not None:
            n, edges = res
            if n > best and consider(n, edges):
                best = n
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    twin_deadline = t0 + 0.35 * budget
    parent_deadline = t0 + 0.5 * budget
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

    # Twin graph on W(d-2), then randomized set-cover extension using spare slots.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, parent_deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    # Non-abelian semidirect-product voltage lifts, searched past the current best.
    if D >= 2 and d >= 2:
        try:
            _lift_phase(d, D, best[0], deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
