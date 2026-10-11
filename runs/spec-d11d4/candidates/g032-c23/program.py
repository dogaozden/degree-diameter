import itertools
import math
import random
import time

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
    c = [0] * n          # number of neighbours of v inside S
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
            # Restart from the best independent set found so far.
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
    padj = [set() for _ in range(P)]          # collinear points
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)
    ladj = [set() for _ in range(L)]          # lines sharing a point
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
# NEW: bi-Cayley (group-lift) search for diameter 4.
#
# Base graph: two vertices A, B with d darts s in S (subset of G, |S| = d).
# Lift on G with |G| = N: a_x ~ b_{x*s} for s in S. Bipartite, degree d,
# 2N vertices. Left multiplication is an automorphism, so G is transitive on
# each side. Diameter <= 4 reduces to coverage from a_e and b_e:
#   A from a_e : walks of length 0,2,4 reach all of G
#   B from a_e : walks of length 1,3 reach all of G
#   B from b_e : walks of length 0,2,4 reach all of G
# Simulated annealing minimizes the total number of uncovered targets.
# ----------------------------------------------------------------------------

def _random_group(N, rng):
    """Return (order, mul, inv) for a random group of order N (cyclic or Z_m x| Z_k), or None."""
    opts = []
    for k in range(1, 13):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        if k == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    if not opts:
        return None
    m, k, r = rng.choice(opts)
    if k == 1:
        return lib.cyclic_group(m)
    return lib.semidirect_group(m, k, r)


def _deficit(S, mt, itab, N):
    """Total number of uncovered targets from a_e and b_e (0 means diameter <= 4)."""
    Si = [itab[s] for s in S]
    # From a_e (A-side walks: a_e -> b_s -> a_{s t^-1} -> ...).
    E2 = set()
    for y in S:
        row = mt[y]
        for t in Si:
            E2.add(row[t])
    E3 = set()
    for x in E2:
        row = mt[x]
        for s in S:
            E3.add(row[s])
    E4 = set()
    for y in E3:
        row = mt[y]
        for t in Si:
            E4.add(row[t])
    dA = N - len(E2 | E4 | {0})
    dB = N - len(set(S) | E3)
    # From b_e (B-side walks: b_e -> a_{t^-1} -> b_{t^-1 s} -> ...).
    F2 = set()
    for x in Si:
        row = mt[x]
        for s in S:
            F2.add(row[s])
    F3 = set()
    for y in F2:
        row = mt[y]
        for t in Si:
            F3.add(row[t])
    F4 = set()
    for x in F3:
        row = mt[x]
        for s in S:
            F4.add(row[s])
    dC = N - len(F2 | F4 | {0})
    return dA + dB + dC


def _anneal(N, d, mt, itab, deadline, rng):
    """Anneal a dart set S of size d in G (|G| = N) until the deficit is 0; return S or None."""
    S = rng.sample(range(N), d)
    cur = _deficit(S, mt, itab, N)
    it = 0
    while cur and time.monotonic() < deadline:
        it += 1
        i = rng.randrange(d)
        g = rng.randrange(N)
        if g in S:
            continue
        cand = S[:]
        cand[i] = g
        nd = _deficit(cand, mt, itab, N)
        phase = (it % 1500) / 1500.0
        T = 0.05 + 2.5 * (1.0 - phase)
        delta = nd - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S, cur = cand, nd
    return S if cur == 0 else None


def _lift_edges(N, S, mt):
    """Edges of the bi-Cayley graph: a_x = x, b_y = N + y, with a_x ~ b_{x*s}."""
    edges = []
    for x in range(N):
        row = mt[x]
        for s in S:
            edges.append((x, N + row[s]))
    return edges


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

    # Parent pipeline (twin graph + extension) now gets only part of the budget,
    # so that the bi-Cayley search below has time to run.
    pdl = t0 + 0.6 * budget
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            twin_deadline = t0 + 0.3 * budget
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            attempt = 0
            while time.monotonic() < pdl - 1.0 and attempt < 4:
                remaining = pdl - time.monotonic()
                slice_end = time.monotonic() + max(1.0, remaining / (4 - attempt))
                n3, e3 = _extend(n2, e2, d, min(slice_end, pdl), rng)
                consider(n3, e3)
                attempt += 1
                if n3 == n2 and attempt >= 2:
                    break
        except Exception:
            pass

    # Bold path: bi-Cayley lifts over groups of order N, aiming to beat the
    # current best order 2N. Every result is validated before being kept.
    if D >= 4 and d >= 3:
        try:
            N = best[0] // 2 + 1
            while time.monotonic() < deadline - 4.0:
                try:
                    grp = _random_group(N, rng)
                except Exception:
                    grp = None
                if grp is None:
                    N += 1
                    continue
                order, mul, inv = grp
                try:
                    mt = [[mul(x, y) for y in range(order)] for x in range(order)]
                    itab = [inv(x) for x in range(order)]
                except Exception:
                    continue
                slice_end = min(deadline - 1.0, time.monotonic() + 12.0)
                S = _anneal(order, d, mt, itab, slice_end, rng)
                if S is not None:
                    consider(2 * order, _lift_edges(order, S, mt))
                    N = best[0] // 2 + 1
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
