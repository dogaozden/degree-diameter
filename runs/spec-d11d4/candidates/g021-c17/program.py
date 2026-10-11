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
# Voltage lifts over small (semidirect) groups, searched by simulated annealing.
#
# Base graph: k A-vertices and k B-vertices, each of degree d, with dart
# multiplicities M (circulant). Lift vertices (A_i, x), (B_j, y), x,y in G.
# Dart (A_i, B_j, g) gives edges (A_i, x)-(B_j, x*g). Left multiplication by G
# is an automorphism, so distances from (u, e) for each base vertex u decide
# the diameter.
# ----------------------------------------------------------------------------

def _semidirect_table(m, t, r):
    """Multiplication table of Z_m x| Z_t (element (a,b) coded a*t+b, (a,b)(c,d) = (a + r^b c, b + d))."""
    N = m * t
    x = np.arange(N, dtype=np.int64)
    a = x // t
    b = x % t
    pw = np.array([pow(r, bb, m) for bb in range(t)], dtype=np.int64)
    A = a[:, None]
    B = b[:, None]
    C = a[None, :]
    Dd = b[None, :]
    return ((A + pw[B] * C) % m) * t + (B + Dd) % t


def _groups(N):
    """Candidate (m, t, r) with group Z_m x| Z_t of order N (t = 1 gives cyclic)."""
    out = [(N, 1, 1)]
    for t in range(2, N + 1):
        if N % t:
            continue
        m = N // t
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, t, m) == 1 % m:
                out.append((m, t, r))
    return out


def _circulant(d, k):
    """Dart multiplicity matrix: row and column sums both equal d."""
    q, rem = divmod(d, k)
    return [[q + (1 if (j - i) % k < rem else 0) for j in range(k)] for i in range(k)]


def _lift_structure(k, d, M):
    AJ = np.zeros((k, d), dtype=np.int64)
    for i in range(k):
        row = []
        for j in range(k):
            row += [j] * M[i][j]
        AJ[i] = row
    AJf = AJ.reshape(-1)
    Bf = np.zeros((k, d), dtype=np.int64)
    cnt = [0] * k
    for f in range(k * d):
        j = int(AJf[f])
        Bf[j, cnt[j]] = f
        cnt[j] += 1
    groups = {}
    for f in range(k * d):
        groups.setdefault((f // d, int(AJf[f])), []).append(f)
    peers = [[p for p in groups[(f // d, int(AJf[f]))] if p != f] for f in range(k * d)]
    return AJ, Bf, groups, peers


def _build_nb(k, d, N, T, inv, AJ, AG2, Bf):
    """Neighbour array (2kN, d) of the lift."""
    BG = AG2.reshape(-1)[Bf]
    BI = Bf // d
    IG = inv[BG]
    M1 = T[:, AG2].transpose(1, 0, 2)
    nbA = (AJ[:, None, :] + k) * N + M1
    M2 = T[:, IG].transpose(1, 0, 2)
    nbB = BI[:, None, :] * N + M2
    return np.concatenate([nbA.reshape(k * N, d), nbB.reshape(k * N, d)], axis=0)


def _unreached(nb, n, roots, D):
    """Total number of vertices not within distance D of the root vertices."""
    tot = 0
    for r in roots:
        vis = np.zeros(n, dtype=bool)
        vis[r] = True
        front = np.array([r], dtype=np.int64)
        for _ in range(D):
            cand = nb[front].ravel()
            cand = cand[~vis[cand]]
            if cand.size == 0:
                break
            front = np.unique(cand)
            vis[front] = True
        tot += n - int(vis.sum())
    return tot


def _search_lift(k, d, N, T, inv, AJ, Bf, groups, peers, D, deadline, rng):
    n = 2 * k * N
    roots = [i * N for i in range(k)] + [(k + j) * N for j in range(k)]
    AG = np.zeros(k * d, dtype=np.int64)
    for fl in groups.values():
        vals = rng.sample(range(N), len(fl))
        for f, v in zip(fl, vals):
            AG[f] = v

    def cost(vec):
        nb = _build_nb(k, d, N, T, inv, AJ, vec.reshape(k, d), Bf)
        return _unreached(nb, n, roots, D)

    cur = cost(AG)
    best = cur
    bestAG = AG.copy()
    start = time.monotonic()
    span = max(1e-6, deadline - start)
    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - start) / span
        temp = 0.15 + 2.0 * (1.0 - frac)
        f = rng.randrange(k * d)
        used = {int(AG[p]) for p in peers[f]}
        old = int(AG[f])
        g = rng.randrange(N)
        while g in used or g == old:
            g = rng.randrange(N)
        AG[f] = g
        c = cost(AG)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
            if c < best:
                best = c
                bestAG = AG.copy()
        else:
            AG[f] = old
    return best, bestAG


def _voltage_search(d, D, deadline, rng):
    """Search lifts that beat the parent order; return (n, edges) of the best found, or None."""
    best = None
    target = 1776
    while time.monotonic() < deadline - 0.5:
        k = rng.choice([2, 2, 3, 3, 4, 5])
        minN = -(-target // (2 * k))
        N = minN + rng.randrange(0, 3)
        opts = _groups(N)
        if not opts:
            continue
        m, t, r = rng.choice(opts)
        T = _semidirect_table(m, t, r)
        inv = np.argmax(T == 0, axis=1).astype(np.int64)
        AJ, Bf, groups, peers = _lift_structure(k, d, _circulant(d, k))
        slice_end = min(deadline, time.monotonic() + 6.0)
        c, AG = _search_lift(k, d, N, T, inv, AJ, Bf, groups, peers, D, slice_end, rng)
        if c == 0:
            nb = _build_nb(k, d, N, T, inv, AJ, AG.reshape(k, d), Bf)
            edges = [(u, int(v)) for u in range(k * N) for v in nb[u]]
            n = 2 * k * N
            if best is None or n > best[0]:
                best = (n, edges)
    return best


# ----------------------------------------------------------------------------
# Parent pipeline (projective plane, GQ, twin + extension) with a time deadline.
# ----------------------------------------------------------------------------

def _parent(d, D, rng, deadline):
    t0 = time.monotonic()
    budget = max(0.5, deadline - t0)
    best = lib.haar_graph(d, range(d))

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
            twin_deadline = t0 + 0.4 * budget
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            attempt = 0
            while time.monotonic() < deadline - 1.0 and attempt < 4:
                remaining = deadline - time.monotonic()
                slice_end = time.monotonic() + max(1.0, remaining / (4 - attempt))
                n3, e3 = _extend(n2, e2, d, min(slice_end, deadline), rng)
                consider(n3, e3)
                attempt += 1
                if n3 == n2 and attempt >= 2:
                    break
        except Exception:
            pass

    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.88 * time_limit, time_limit - 7.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    if d == 11 and D == 4:
        # Parent gives the safe result; the voltage-lift search tries to beat it.
        best = _parent(d, D, rng, t0 + 0.35 * budget)
        try:
            cand = _voltage_search(d, D, deadline - 1.0, rng)
        except Exception:
            cand = None
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    else:
        best = _parent(d, D, rng, deadline)

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
