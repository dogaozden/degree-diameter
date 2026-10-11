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
# NEW CONSTRUCTION: multi-vertex bi-Cayley lifts with SA over voltages.
#
# Base: k "A" vertices and k "B" vertices, d-regular bipartite multigraph formed
# by d permutations sigma_t of range(k). Dart (t, i) joins A_i to B_{sigma_t(i)}
# with voltage g in a finite group G of order N. Lifted vertices (A_i, x) and
# (B_j, y), with (A_i, x) ~ (B_j, x*g).
#
# Left translation by h is an automorphism of the lift, so the diameter is at
# most D iff every representative (A_i, e) and (B_j, e) reaches all vertices
# within D steps. This is checked cheaply with numpy ball expansion. SA moves
# change voltages and swap entries of the permutations. Every result is
# verified with lib.is_valid before use.
# ----------------------------------------------------------------------------

def _group_options(N):
    """Return (m, k, r) choices giving groups of order N: cyclic Z_N and Z_m x|_r Z_k."""
    opts = [(N, 1, 1)]
    for k in range(2, N + 1):
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


def _lift_nbr(k, d, N, MT, inv, sigma, volt):
    """Neighbour array (n x d) of the lift. A_i block is rows i*N.., B_j block is rows k*N + j*N.."""
    n = 2 * k * N
    nbr = np.empty((n, d), dtype=np.int64)
    base_b = k * N
    for t in range(d):
        for i in range(k):
            j = int(sigma[t, i])
            g = int(volt[t, i])
            gi = int(inv[g])
            nbr[i * N:(i + 1) * N, t] = base_b + j * N + MT[:, g]
            nbr[base_b + j * N: base_b + (j + 1) * N, t] = i * N + MT[:, gi]
    return nbr


def _lift_cost(k, D, N, nbr):
    """Number of (representative, vertex) pairs not within distance D; 0 means diameter <= D."""
    n = nbr.shape[0]
    reps = [i * N for i in range(k)] + [k * N + j * N for j in range(k)]
    R = len(reps)
    mask = np.zeros((R, n), dtype=bool)
    mask[np.arange(R), reps] = True
    for _ in range(D):
        mask = mask | mask[:, nbr].any(axis=2)
    return R * n - int(mask.sum())


def _lift_sa(k, d, D, N, MT, inv, deadline, rng):
    """SA over (sigma, volt) for one group; return (sigma, volt) with diameter <= D, or None."""
    sigma = np.array([rng.sample(range(k), k) for _ in range(d)], dtype=np.int64)
    volt = np.array([[rng.randrange(N) for _ in range(k)] for _ in range(d)], dtype=np.int64)
    nbr = _lift_nbr(k, d, N, MT, inv, sigma, volt)
    cur = _lift_cost(k, D, N, nbr)
    t_start = time.monotonic()
    span = max(deadline - t_start, 1e-6)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t_start) / span
        T = 0.3 + 6.0 * (1.0 - frac)
        s2 = sigma.copy()
        v2 = volt.copy()
        t = rng.randrange(d)
        if k > 1 and rng.random() < 0.15:
            a, b = rng.sample(range(k), 2)
            s2[t, a], s2[t, b] = s2[t, b], s2[t, a]
        else:
            i = rng.randrange(k)
            v2[t, i] = rng.randrange(N)
        nbr2 = _lift_nbr(k, d, N, MT, inv, s2, v2)
        c2 = _lift_cost(k, D, N, nbr2)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            sigma, volt, nbr, cur = s2, v2, nbr2, c2
    return sigma, volt


def _lift_try_N(k, d, D, N, kdead, rng):
    """Try random groups of order N with SA until kdead; return (MT, inv, sigma, volt) or None."""
    opts = _group_options(N)
    while time.monotonic() < kdead:
        m, kk, r = rng.choice(opts)
        MT = _mul_table(m, kk, r)
        inv = np.argmax(MT == 0, axis=1).astype(np.int64)
        sub_end = min(kdead, time.monotonic() + 0.8)
        st = _lift_sa(k, d, D, N, MT, inv, sub_end, rng)
        if st is not None:
            return MT, inv, st[0], st[1]
    return None


def _lift_edges(nbr):
    """Deduplicated sorted edge list of the lift."""
    edges = set()
    for p, row in enumerate(nbr.tolist()):
        for q in row:
            edges.add((p, q) if p < q else (q, p))
    return sorted(edges)


def _lift_search(d, D, moore, best_n, deadline, rng):
    """Bisection over base size k and group order N; return (n, edges) of the best valid lift, or None."""
    best = None
    cur = best_n
    ks = [2, 3, 4, 1, 5, 6, 8]
    for idx, k in enumerate(ks):
        now = time.monotonic()
        if now >= deadline:
            break
        kdead = now + (deadline - now) / (len(ks) - idx)
        hi = moore // (2 * k)
        lo = max(2, cur // (2 * k) + 1)
        while lo <= hi and time.monotonic() < kdead:
            N = (lo + hi + 1) // 2
            res = _lift_try_N(k, d, D, N, kdead, rng)
            if res is None:
                hi = N - 1
                continue
            MT, inv, sigma, volt = res
            nbr = _lift_nbr(k, d, N, MT, inv, sigma, volt)
            n = 2 * k * N
            edges = _lift_edges(nbr)
            if n > cur and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                cur = n
            lo = N + 1
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

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

    # Already at the Moore bound: nothing to gain.
    if best[0] >= moore:
        return best

    # New bold path: multi-vertex bi-Cayley lifts with SA over voltages.
    if D >= 2 and d >= 3:
        try:
            res = _lift_search(d, D, moore, best[0], t0 + 0.4 * budget, rng)
            if res is not None:
                consider(*res)
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
